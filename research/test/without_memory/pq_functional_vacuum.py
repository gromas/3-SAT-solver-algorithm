import sys
import time
try:
    from dd.autoref import BDD
except ImportError:
    print("Ошибка: Установите библиотеку dd (pip install dd)")
    sys.exit(1)

class PQFunctionalVacuum:
    def __init__(self, vars_count, clauses):
        self.n = vars_count
        self.clauses = clauses
        self.bdd = BDD()
        
        # Декларируем переменные
        for i in range(1, self.n + 1):
            self.bdd.declare(f'x{i}')
        
        # Функции литералов: зависят от переменных с МЕНЬШИМИ индексами
        self.f_pos = {i: self.bdd.true for i in range(1, self.n + 1)}
        self.f_neg = {i: self.bdd.true for i in range(1, self.n + 1)}
        
        self._build_pq_structure()

    def _build_pq_structure(self):
        for clause in self.clauses:
            if not clause: continue
            # Сортируем по убыванию (от n к 1), чтобы ведущий был МАКСИМАЛЬНЫМ
            # В твоем PQ-разложении: xi определяется через xj, где j < i
            sorted_lits = sorted(clause, key=lambda l: abs(l), reverse=True)
            lead_lit = sorted_lits[0]
            idx = abs(lead_lit)
            
            # Остаток: (L2 v L3)
            rest_bdd = self.bdd.false
            for lit in sorted_lits[1:]:
                var_name = f'x{abs(lit)}'
                node = self.bdd.add_expr(var_name if lit > 0 else f'~{var_name}')
                rest_bdd |= node
            
            # Если x_i=True, то при наличии x_i в дизъюнкте ограничений нет.
            # Ограничение накладывается, если x_i принимает значение, ПУСТОЕ в дизъюнкте.
            if lead_lit > 0:
                self.f_neg[idx] &= rest_bdd
            else:
                self.f_pos[idx] &= rest_bdd

    def solve(self):
        start_time = time.time()
        # Включаем оптимизацию памяти в менеджере
        self.bdd.configure(reordering=True) 
        
        residue = self.bdd.true
        max_nodes = 0

        for i in range(self.n, 0, -1):
            var_name = f'x{i}'
            
            # Агрессивное слияние
            current_constraints = (self.bdd.add_expr(var_name) & self.f_pos[i]) | \
                                  (self.bdd.add_expr(f"~{var_name}") & self.f_neg[i])
            
            residue &= current_constraints
            residue = self.bdd.exist([var_name], residue)
            
            # ЧИСТКА ПАМЯТИ - критично!
            if i % 5 == 0:
                self.bdd.collect_garbage()
            
            nodes_count = len(residue)
            max_nodes = max(max_nodes, nodes_count)

            if i % 10 == 0 or i <= 5:
                print(f"Step {i:3} | Nodes: {nodes_count:7} | Max: {max_nodes:7} | Time: {time.time()-start_time:.2f}s")
            
            if residue == self.bdd.false:
                return "UNSAT"

        return "SAT"
