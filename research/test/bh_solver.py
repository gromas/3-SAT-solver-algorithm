import sys
import time
import os
from dd.autoref import BDD

class BlackHoleSolver:
    def __init__(self, vars_count, clauses):
        self.n = vars_count
        self.clauses = clauses
        self.bdd_manager = BDD()
        
        # Регистрация переменных
        for i in range(1, self.n + 1):
            self.bdd_manager.declare(f'x{i}')
        
        # Список всех активных BDD-ограничений (дизъюнктов)
        self.constraints = []
        self._initialize_constraints()

    def _initialize_constraints(self):
        print(f"📦 Построение начальных BDD для {len(self.clauses)} клауз...")
        for clause in self.clauses:
            if not clause: continue
            clause_bdd = self.bdd_manager.false
            for lit in clause:
                v_name = f'x{abs(lit)}'
                node = self.bdd_manager.add_expr(v_name if lit > 0 else f'~{v_name}')
                clause_bdd |= node
            self.constraints.append(clause_bdd)

    def solve(self):
        print(f"🕳️ Запуск BlackHole Solver | N: {self.n}")
        start_time = time.time()
        
        # Множество переменных, которые еще не элиминированы
        active_vars = set(range(1, self.n + 1))
        
        step = 0
        while active_vars:
            step += 1
            
            # 1. Анализируем текущие зависимости: в каких BDD участвует каждая переменная
            # Это необходимо для честной элиминации без потери конфликтов
            var_to_bdds = {v: [] for v in active_vars}
            var_weights = {v: 0 for v in active_vars}
            
            for bdd in self.constraints:
                support = self.bdd_manager.support(bdd)
                for v_name in support:
                    v_idx = int(v_name[1:])
                    if v_idx in active_vars:
                        var_to_bdds[v_idx].append(bdd)
                        var_weights[v_idx] += len(bdd) # Вес = сумма узлов графов

            # 2. ЖАДНЫЙ ВЫБОР: выбираем переменную с минимальным весом участия
            # Это минимизирует "взрыв" при операции OR (exist)
            candidates = [v for v in active_vars if var_to_bdds[v]]
            
            if not candidates:
                # Если переменные остались, но ограничений на них нет - это SAT
                break
                
            best_var = min(candidates, key=lambda v: var_weights[v])
            var_name = f'x{best_var}'
            
            # 3. СБОР ВСЕХ ОГРАНИЧЕНИЙ: вынимаем ВСЕ BDD, где есть best_var
            # Это критически важно: нельзя "забыть" ни одну связь
            related_bdds = var_to_bdds[best_var]
            
            # Оставляем только те BDD, которые НЕ содержат нашу переменную
            new_constraints = [b for b in self.constraints if b not in related_bdds]
            
            # 4. ЛОКАЛЬНЫЙ СИНТЕЗ: перемножаем все связанные BDD в один блок
            local_block = self.bdd_manager.true
            for b in related_bdds:
                local_block &= b
                
            if local_block == self.bdd_manager.false:
                print(f"❌ UNSAT на шаге {step} (конфликт в блоке {var_name})")
                return False

            # 5. АННИГИЛЯЦИЯ (Схлопывание измерения)
            # residue = (Block[x=1] | Block[x=0])
            residue = self.bdd_manager.exist([var_name], local_block)
            
            if residue == self.bdd_manager.false:
                print(f"❌ UNSAT на шаге {step} (противоречие при элиминации {var_name})")
                return False

            # Обновляем список ограничений: добавляем "осадок" (residue)
            self.constraints = new_constraints
            if residue != self.bdd_manager.true:
                self.constraints.append(residue)
            
            active_vars.remove(best_var)

            if step % 5 == 0 or len(active_vars) < 5:
                elapsed = time.time() - start_time
                print(f"  Шаг {step:3} | Убита: {var_name:4} | Вес: {var_weights[best_var]:6} | BDDs: {len(self.constraints):3} | Time: {elapsed:.2f}s")

        print(f"✅ SAT подтвержден за {time.time() - start_time:.4f} сек!")
        return True

def parse_dimacs(file_path):
    if not os.path.exists(file_path): return None, None
    clauses, vars_count = [], 0
    try:
        with open(file_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith(('c', '%', '0')): continue
                if line.startswith('p cnf'):
                    parts = line.split()
                    vars_count = int(parts[2])
                    continue
                row = []
                for x in line.split():
                    try:
                        val = int(x)
                        if val == 0: break
                        row.append(val)
                    except ValueError: continue
                if row: clauses.append(row)
    except: return None, None
    return vars_count, clauses

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Использование: python solver.py <path_to_cnf>")
        sys.exit(1)
        
    v_count, cls = parse_dimacs(sys.argv[1])
    if v_count:
        solver = BlackHoleSolver(v_count, cls)
        solver.solve()
