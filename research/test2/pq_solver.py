# pq_solver.py
import os
import sys
import time
import gc
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
        bdd = self.bdd_manager.true
        
        for clause in clauses:
            clause_bdd = self.bdd_manager.false
            for lit in clause:
                var_name = f'x{abs(lit)}'
                if lit > 0:
                    lit_bdd = self.bdd_manager.var(var_name)
                else:
                    lit_bdd = ~self.bdd_manager.var(var_name)
                clause_bdd = clause_bdd | lit_bdd
            
            bdd = bdd & clause_bdd
        
        return bdd

    def _split_clauses_by_variable(self) -> List[List[List[int]]]:
        """
        Разделяет клозы по переменным.
        Каждый клоз попадает только в одну группу - к переменной с минимальным индексом.
        """
        var_clauses = [[] for _ in range(self.n_vars + 1)]
        
        for clause in self.original_clauses:
            min_var = min(abs(lit) for lit in clause)
            var_clauses[min_var].append(clause)
        
        return var_clauses
        
    def find_unique_support_variables(self, combined, current_idx: int) -> List[int]:
        """
        Находит переменные, которые есть в поддержке BDD с индексом current_idx,
        но отсутствуют во всех остальных активных BDD.
        
        Возвращает список переменных (их ID) для возможной элиминации.
        """
        
        #if current_idx >= len(self.variables):
        #    return []
        
        #current_bdd = self.variables[current_idx].bdd
        #if current_bdd == self.bdd_manager.true:
        #    return []
        
        current_support = set(combined.support)
        if not current_support:
            return []
        
        other_supports = set()
        for idx, var_bdd in enumerate(self.variables):
            if idx == current_idx or var_bdd.bdd == self.bdd_manager.true:
                continue
            other_supports.update(var_bdd.bdd.support)
        
        unique_vars = current_support - other_supports
        
        result = []
        for var_name in unique_vars:
            if var_name.startswith('x'):
                try:
                    var_id = int(var_name[1:])
                    result.append(var_id)
                except ValueError:
                    continue
        
        return result        

    def solve(self, filename: str) -> Tuple[bool, Dict]:
        """
        Основной метод решения.
        Возвращает (результат: SAT=True/UNSAT=False, статистика)
        """
        is_sat = True
        start_total = time.time()
        
        # Шаг 1: Инициализация и загрузка
        print("\n" + "="*70)
        print("🔧 ШАГ 1: Инициализация и построение BDD для переменных")
        print("="*70)
        
        self.n_vars, self.original_clauses = parse_dimacs_cnf(filename)
        print(f"\n📊 Исходная функция F:")
        print(f"   Переменных: {self.n_vars}")
        print(f"   Клозов: {len(self.original_clauses)}")
        print(f"   Плотность: {len(self.original_clauses)/self.n_vars:.2f}")
        
        var_order = {f'x{i}': i for i in range(self.n_vars, 0, -1)}
        self.bdd_manager = _bdd.BDD()
        for i in range(self.n_vars, 0, -1):
            self.bdd_manager.declare(f'x{i}')
        
        var_clauses = self._split_clauses_by_variable()
        
        for var_id in range(1, self.n_vars + 1):
            if not var_clauses[var_id]:
                print(f"\n⚠️  Переменная x{var_id} не имеет клозов - пропускаем")
                continue
                
            start_step = time.time()
            
            print(f"\n📌 Шаг 1.{var_id}: Обработка переменной x{var_id}")
            print(f"   Клозов с этой переменной: {len(var_clauses[var_id])}")
            
            bdd = self._create_bdd_for_variable(var_id, var_clauses[var_id])

            if bdd == self.bdd_manager.false:
                print(f"❌ Обнаружено противоречие при построении x{var_id}")
                return False
            node_count = len(self.bdd_manager)
            
            self.variables.append(VariableBDD(var_id, bdd, var_clauses[var_id]))
            
            step_time = time.time() - start_step
            self.stats['step1_times'].append(step_time)
            
            print(f"   ✅ BDD создан. Размер: {node_count} узлов")
            print(f"   ⏱️  Время: {step_time:.3f} сек")
        
        print(f"\n✅ Шаг 1 завершён. Построено BDD для {len(self.variables)} переменных")
        
        # Шаг 2: Композиция BDD (НОВАЯ ОПТИМИЗИРОВАННАЯ ВЕРСИЯ)
        print("\n" + "="*70)
        print("🔄 ШАГ 2: Композиция BDD (с промежуточной оптимизацией)")
        print("="*70)
        
        step2_count = 0
       
        for i in range(len(self.variables) - 1, -1, -1):
            if self.variables[i].bdd == self.bdd_manager.true:
                continue
                
            var_i = self.variables[i]
            var_name = f'x{var_i.var_id}'
            
            # Текущий накапливаемый BDD
            current = self.variables[i].bdd
            self.variables[i].bdd = self.bdd_manager.true
            min_j = i
            
            # Перебираем все BDD с меньшим индексом
            for j in reversed(range(i)):
                if self.variables[j].bdd == self.bdd_manager.true:
                    continue
                    
                if var_name in self.variables[j].bdd.support:
                    min_j = j
                    start_step = time.time()
                    step2_count += 1
                    
                    print(f"\n📌 Шаг 2.{step2_count}: Композиция x{self.variables[j].var_id} := compose(x{var_i.var_id})")
                    print(f"   До композиции: {len(self.bdd_manager)} узлов")
                    
                    # 1. Объединяем с текущим BDD
                    current = current & self.variables[j].bdd
                    self.variables[j].bdd = self.bdd_manager.true
                    
                    # 2. ПРОМЕЖУТОЧНАЯ ОПТИМИЗАЦИЯ: элиминируем уникальные переменные
                    unique = self.find_unique_support_variables(current, min_j)
                    if unique:
                        print(f"   🎯 Промежуточные уникальные в x{self.variables[min_j].var_id}: {unique}")
                        for var_id in unique:
                            var_name_unique = f'x{var_id}'
                            current = current.exist(var_name_unique)
                            print(f"      ✅ Элиминирована x{var_id}")
                    
                    print(f"   После: {len(self.bdd_manager)} узлов")
                    
                    step_time = time.time() - start_step
                    self.stats['step2_times'].append(step_time)
            
            # Финальная элиминация xi
            start_step = time.time()
            current = current.exist(var_name)
            
            # Финальная оптимизация
            unique = self.find_unique_support_variables(current, min_j)
            if unique:
                print(f"\n📌 Финальные уникальные в x{self.variables[min_j].var_id}: {unique}")
                for var_id in unique:
                    var_name_unique = f'x{var_id}'
                    current = current.exist(var_name_unique)
                    print(f"   ✅ Элиминирована x{var_id}")
            
            self.variables[min_j].bdd = current
            
            if current == self.bdd_manager.false:
                is_sat = False
                
            step_time = time.time() - start_step
            self.stats['step2_times'].append(step_time)
        
        print(f"\n✅ Шаг 2 завершён. Выполнено {step2_count} композиций")
        
        # Шаг 3: Проверка выполнимости
        print("\n" + "="*70)
        print("🔍 ШАГ 3: Проверка выполнимости")
        print("="*70)

        if is_sat:
            final_bdd = self.variables[0].bdd
            self.stats['final_bdd_size'] = len(self.bdd_manager)
            
            print(f"\n📊 Финальный BDD (переменная x{self.variables[0].var_id}):")
            print(f"   Размер менеджера: {self.stats['final_bdd_size']} узлов")
            
            model_iterator = self.bdd_manager.pick_iter(final_bdd)
            
            try:
                first_model = next(model_iterator)
                is_sat = True
                result = "SAT"
                
                print(f"\n🎯 Результат: {result}")
                print(f"\n📝 Пример выполняющего набора:")
                for var, val in sorted(first_model.items()):
                    if var.startswith('x'):
                        print(f"   {var} = {val}")
                        
            except StopIteration:
                is_sat = False
                result = "UNSAT"
                print(f"\n🎯 Результат: {result}")
                
        else:
            print("\n⚠️  Нет построенных BDD")
            is_sat = False
            result = "UNSAT (пустая формула?)"
        
        self.stats['total_time'] = time.time() - start_total
        
        print("\n" + "="*70)
        print("📈 ИТОГОВАЯ СТАТИСТИКА")
        print("="*70)
        print(f"⏱️  Общее время выполнения: {self.stats['total_time']:.3f} сек")
        print(f"📊 Время по шагам:")
        print(f"   Шаг 1 (построение): {sum(self.stats['step1_times']):.3f} сек")
        print(f"   Шаг 2 (композиция): {sum(self.stats['step2_times']):.3f} сек")
        if self.stats['step2_times']:
            print(f"   Среднее время композиции: {sum(self.stats['step2_times'])/len(self.stats['step2_times']):.3f} сек")
        else:
            print("   Нет композиций")
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
