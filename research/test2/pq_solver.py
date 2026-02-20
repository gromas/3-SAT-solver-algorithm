# pq_solver.py
import os
import sys
import time
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
import dd.autoref as _bdd

# Импортируем загрузчик DIMACS
try:
    from dimacs_loader import parse_dimacs_cnf, print_benchmark_info
except ImportError:
    print("Ошибка: dimacs_loader.py не найден. Убедитесь, что файл находится в той же директории.")
    sys.exit(1)


@dataclass
class VariableBDD:
    """Класс для хранения BDD переменной и связанных с ней клозов"""
    var_id: int  # Идентификатор переменной
    bdd: _bdd.BDD  # BDD для этой переменной
    clauses: List[List[int]]  # Клозы, содержащие эту переменную


class PQBDDSolver:
    def __init__(self):
        self.bdd_manager: Optional[_bdd.BDD] = None
        self.variables: List[VariableBDD] = []  # Список в порядке создания
        self.n_vars: int = 0
        self.original_clauses: List[List[int]] = []
        self.stats = {
            'total_time': 0,
            'step1_times': [],
            'step2_times': [],
            'final_bdd_size': 0
        }

    def _create_bdd_for_variable(self, var_id: int, clauses: List[List[int]]) -> _bdd.BDD:
        """
        Создаёт BDD для конкретной переменной, учитывая все клозы с её литералами.
        Порядок переменных: от n до 1 (убывающий)
        """
        # Создаём BDD для конъюнкции клозов, содержащих эту переменную
        bdd = self.bdd_manager.true
        
        for clause in clauses:
            # Создаём BDD для дизъюнкта
            clause_bdd = self.bdd_manager.false
            for lit in clause:
                var_name = f'x{abs(lit)}'
                if lit > 0:
                    lit_bdd = self.bdd_manager.var(var_name)
                else:
                    lit_bdd = ~self.bdd_manager.var(var_name)
                clause_bdd = clause_bdd | lit_bdd
            
            # Конъюнкция всех клозов
            bdd = bdd & clause_bdd
        
        return bdd

    def _split_clauses_by_variable(self) -> List[List[List[int]]]:
        """
        Разделяет клозы по переменным.
        Каждый клоз попадает только в одну группу - к переменной с минимальным индексом.
        """
        # Сортируем клозы по минимальному индексу переменной в них
        var_clauses = [[] for _ in range(self.n_vars + 1)]  # 1-based индексация
        
        for clause in self.original_clauses:
            # Находим минимальную переменную в клозе
            min_var = min(abs(lit) for lit in clause)
            var_clauses[min_var].append(clause)
        
        return var_clauses

    def solve(self, filename: str) -> Tuple[bool, Dict]:
        """
        Основной метод решения.
        Возвращает (результат: SAT=True/UNSAT=False, статистика)
        """
        start_total = time.time()
        
        # Шаг 1: Инициализация и загрузка
        print("\n" + "="*70)
        print("🔧 ШАГ 1: Инициализация и построение BDD для переменных")
        print("="*70)
        
        # Парсим CNF файл
        self.n_vars, self.original_clauses = parse_dimacs_cnf(filename)
        print(f"\n📊 Исходная функция F:")
        print(f"   Переменных: {self.n_vars}")
        print(f"   Клозов: {len(self.original_clauses)}")
        print(f"   Плотность: {len(self.original_clauses)/self.n_vars:.2f}")
        
        # Инициализируем BDD менеджер с порядком переменных от n до 1
        var_order = {f'x{i}': i for i in range(self.n_vars, 0, -1)}
        self.bdd_manager = _bdd.BDD()
        for i in range(self.n_vars, 0, -1):
            self.bdd_manager.declare(f'x{i}')
        
        # Разделяем клозы по переменным
        var_clauses = self._split_clauses_by_variable()
        
        # Строим BDD для каждой переменной
        for var_id in range(1, self.n_vars + 1):
            if not var_clauses[var_id]:
                print(f"\n⚠️  Переменная x{var_id} не имеет клозов - пропускаем")
                continue
                
            start_step = time.time()
            
            print(f"\n📌 Шаг 1.{var_id}: Обработка переменной x{var_id}")
            print(f"   Клозов с этой переменной: {len(var_clauses[var_id])}")
            
            # Создаём BDD для этой переменной
            bdd = self._create_bdd_for_variable(var_id, var_clauses[var_id])
            # Блокируем переменную, что бы менеджер не удалил её
            x = self.bdd_manager.var(f'x{var_id}')
            # Проверяем, что текущая bdd не является постоянно ложной
            bdd = bdd & (x | ~x)
            if bdd == self.bdd_manager.false:
                print(f"❌ Обнаружено противоречие при построении x{var_id}")
                return False  # UNSAT
            node_count = len(self.bdd_manager)
            
            self.variables.append(VariableBDD(var_id, bdd, var_clauses[var_id]))
            
            step_time = time.time() - start_step
            self.stats['step1_times'].append(step_time)
            
            print(f"   ✅ BDD создан. Размер: {node_count} узлов")
            print(f"   ⏱️  Время: {step_time:.3f} сек")
        
        print(f"\n✅ Шаг 1 завершён. Построено BDD для {len(self.variables)} переменных")
        
        # Шаг 2: Композиция BDD
        print("\n" + "="*70)
        print("🔄 ШАГ 2: Композиция BDD")
        print("="*70)
        
        step2_count = 0
        # Перебираем BDD в обратном порядке создания (с последней созданной)
        for i in range(len(self.variables) - 1, -1, -1):
            var_i = self.variables[i]
            var_name = f'x{var_i.var_id}'
            #var_i.bdd = self.bdd_manager.exist([var_name], var_i.bdd)  # ∃x_i. BDD_i
            
            # Перебираем все BDD с меньшим индексом переменной
            for j in range(i):
                var_j = self.variables[j]
                
                start_step = time.time()
                step2_count += 1
                
                print(f"\n📌 Шаг 2.{step2_count}: Композиция x{var_j.var_id} := compose(x{var_i.var_id})")
                
                # Статистика до композиции
                #clauses_i = len(var_i.clauses)
                #clauses_j_in = len(var_j.clauses)
                size_j_in = len(self.bdd_manager)
                
                print(f"   До композиции:")
                print(f"     BDD_{var_j.var_id}: {size_j_in} узлов")
                
                # Выполняем композицию: var_j.bdd = compose(var_j.bdd, xi, var_i.bdd)
                # Используем let вместо compose
                var_j.bdd = self.bdd_manager.let({var_name: var_i.bdd}, var_j.bdd)
                #var_j.bdd = self.bdd_manager.exist([var_name], var_j.bdd)  # ∃x_i. BDD_i

                if var_j.bdd == self.bdd_manager.false:
                    print(f"❌ Обнаружено противоречие при композиции x{var_j.var_id} и x{var_i.var_id}")
                    return False  # UNSAT
                
                # Обновляем клозы в var_j (теперь они включают клозы из var_i)
                #var_j.clauses.extend(var_i.clauses)

                # Статистика после композиции
                #clauses_j_out = len(var_j.clauses)
                size_j_out = len(self.bdd_manager)
                # Если размер резко вырос, возможно, это из-за сложных ограничений
                if size_j_out > size_j_in * 10:
                    print(f"⚠️  Резкий рост размера: {size_j_in} → {size_j_out}")                    

                step_time = time.time() - start_step
                self.stats['step2_times'].append(step_time)
                
                print(f"   После композиции:")
                print(f"     BDD_{var_j.var_id}: {size_j_out} узлов")
                print(f"   ⏱️  Время: {step_time:.3f} сек")
        
        print(f"\n✅ Шаг 2 завершён. Выполнено {step2_count} композиций")
        
        # Шаг 3: Проверка выполнимости
        print("\n" + "="*70)
        print("🔍 ШАГ 3: Проверка выполнимости")
        print("="*70)

        # Берём BDD с наименьшей переменной
        if self.variables:
            final_bdd = self.variables[0].bdd  # Первый в списке - с наименьшей переменной
            self.stats['final_bdd_size'] = len(self.bdd_manager)
            
            print(f"\n📊 Финальный BDD (переменная x{self.variables[0].var_id}):")
            print(f"   Размер менеджера: {self.stats['final_bdd_size']} узлов")
            
            # ✅ ПРАВИЛЬНО: используем pick_iter для проверки выполнимости
            # pick_iter возвращает итератор по выполняющим наборам
            model_iterator = self.bdd_manager.pick_iter(final_bdd)
            
            try:
                # Пытаемся получить первую модель
                first_model = next(model_iterator)
                is_sat = True
                result = "SAT"
                
                print(f"\n🎯 Результат: {result}")
                
                # Показываем модель
                print(f"\n📝 Пример выполняющего набора:")
                for var, val in sorted(first_model.items()):
                    if var.startswith('x'):  # Только переменные из формулы
                        print(f"   {var} = {val}")
                        
            except StopIteration:
                # Нет ни одной модели - формула невыполнима
                is_sat = False
                result = "UNSAT"
                print(f"\n🎯 Результат: {result}")
                
        else:
            print("\n⚠️  Нет построенных BDD")
            is_sat = False
            result = "UNSAT (пустая формула?)"
        
        # Общая статистика
        self.stats['total_time'] = time.time() - start_total
        
        print("\n" + "="*70)
        print("📈 ИТОГОВАЯ СТАТИСТИКА")
        print("="*70)
        print(f"⏱️  Общее время выполнения: {self.stats['total_time']:.3f} сек")
        print(f"📊 Время по шагам:")
        print(f"   Шаг 1 (построение): {sum(self.stats['step1_times']):.3f} сек")
        print(f"   Шаг 2 (композиция): {sum(self.stats['step2_times']):.3f} сек")
        print(f"   Среднее время композиции: {sum(self.stats['step2_times'])/len(self.stats['step2_times']):.3f} сек" if self.stats['step2_times'] else "   Нет композиций")
        print(f"📦 Финальный размер BDD: {self.stats['final_bdd_size']} узлов")
        print(f"🎯 Результат: {result}")
        
        return is_sat, self.stats


def main():
    if len(sys.argv) != 2:
        print("Использование: py pq_solver.py <filename.cnf>")
        print("\nПример:")
        print("  py pq_solver.py benchmarks/uf20-01.cnf")
        sys.exit(1)
    
    filename = sys.argv[1]
    
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    print("\n" + "="*70)
    print("🚀 PQ-BDD SAT SOLVER")
    print("="*70)
    print(f"Файл: {filename}")
    
    # Создаём и запускаем солвер
    solver = PQBDDSolver()
    try:
        result, stats = solver.solve(filename)
    except Exception as e:
        print(f"\n❌ Ошибка при решении: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
