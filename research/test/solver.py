import sys
import time
import os
from dd.autoref import BDD

def load_dimacs(file_path):
    if not os.path.exists(file_path):
        return None, None
    clauses = []
    n_vars = 0
    try:
        with open(file_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('c'): continue
                if line.startswith('p'):
                    parts = line.split()
                    n_vars = int(parts[2])
                    continue
                clause = [int(x) for x in line.split()[:-1]]
                if clause: clauses.append(clause)
    except Exception as e:
        print(f"Error reading file: {e}")
        return None, None
    return n_vars, clauses

class PQCausalSweepSolver:
    def __init__(self, n_vars, clauses):
        self.n = n_vars
        self.clauses = clauses
        self.manager = BDD()
        # Декларируем переменные x1...xn
        for i in range(1, n_vars + 1):
            self.manager.declare(f'x{i}')
        
        # Функции для каждой переменной (инициализируем True)
        self.p_funcs = {i: self.manager.true for i in range(1, n_vars + 1)}
        self.global_residue = self.manager.true

    def build_initial_structure(self):
        """
        Статическая фаза P/Q: распределяем клаузы по минимальному индексу.
        """
        for clause in self.clauses:
            if not clause: continue
            sorted_lits = sorted(clause, key=lambda x: abs(x))
            first = sorted_lits[0]
            rest = sorted_lits[1:]
            
            # Формируем выражение: (first | rest)
            expr_parts = []
            for l in rest:
                var_name = f"x{abs(l)}"
                expr_parts.append(f"{'~' if l < 0 else ''}{var_name}")
            
            rest_expr = " | ".join(expr_parts) if expr_parts else "False"
            first_var = f"x{abs(first)}"
            first_prefix = '~' if first < 0 else ''
            
            # Создаем BDD для дизъюнкта
            clause_bdd = self.manager.add_expr(f"{first_prefix}{first_var} | {rest_expr}")
            
            # Добавляем в конъюнкцию бакета первой переменной
            self.p_funcs[abs(first)] &= clause_bdd

    def solve(self):
        start_time = time.time()
        self.build_initial_structure()
        
        print(f"[*] Анализ {self.n} переменных...")
        
        # ОБРАТНЫЙ ПРОХОД (Causal Sweep) от n до 1
        for i in range(self.n, 0, -1):
            var_i = f'x{i}'
            bucket = []
            
            # 1. Собираем функции, зависящие от x_i
            # Используем self.manager.support(node) вместо node.variables
            for j in list(self.p_funcs.keys()):
                if j > i: continue # Оптимизация: j всегда <= i в нашей модели
                
                node = self.p_funcs[j]
                if var_i in self.manager.support(node):
                    bucket.append(node)
                    self.p_funcs[j] = self.manager.true
            
            if var_i in self.manager.support(self.global_residue):
                bucket.append(self.global_residue)
                self.global_residue = self.manager.true

            if not bucket:
                continue

            # 2. КОНЪЮНКЦИЯ (Сшиваем все условия, где участвует x_i)
            combined = self.manager.true
            for f in bucket:
                combined &= f

            # 3. ЭЛИМИНАЦИЯ (Existential Quantification: F(x=1) | F(x=0))
            new_combined = self.manager.exist([var_i], combined)

            # 4. ПРОВЕРКА НА UNSAT
            if new_combined == self.manager.false:
                return "UNSAT", time.time() - start_time

            # 5. ПЕРЕРАСПРЕДЕЛЕНИЕ (Перенос резольвенты влево)
            support = self.manager.support(new_combined)
            if support:
                # Находим переменную с максимальным индексом среди оставшихся
                # Например, из {'x5', 'x12'} выберем 12
                max_idx = max([int(v[1:]) for v in support])
                self.p_funcs[max_idx] &= new_combined
            else:
                # Если зависимостей не осталось (константа True)
                self.global_residue &= new_combined

        return "SAT", time.time() - start_time

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python solver.py <file.cnf>")
        sys.exit(1)
        
    path = sys.argv[1]
    n_vars, clauses = load_dimacs(path)
    
    if n_vars is None:
        sys.exit(1)
        
    solver = PQCausalSweepSolver(n_vars, clauses)
    result, duration = solver.solve()
    
    print(f"\n" + "="*40)
    print(f"Файл: {os.path.basename(path)}")
    print(f"Результат: {result}")
    print(f"Время: {duration:.4f} сек")
    print("="*40)
