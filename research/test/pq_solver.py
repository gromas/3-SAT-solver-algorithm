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
        
        # Декларируем переменные x1, x2, ..., xn
        for i in range(1, self.n + 1):
            self.bdd.declare(f'x{i}')
        
        # Функции литералов: f_pos[i] - условия при xi=1, f_neg[i] - при xi=0
        # Каждая функция зависит ТОЛЬКО от переменных xj, где j > i
        self.f_pos = {i: self.bdd.true for i in range(1, self.n + 1)}
        self.f_neg = {i: self.bdd.true for i in range(1, self.n + 1)}
        
        self._build_pq_structure()

    def _build_pq_structure(self):
        """
        Строит начальное PQ-разложение.
        Для каждого дизъюнкта (L1 v L2 v L3) находим литерал с минимальным индексом.
        Остаток дизъюнкта становится условием для этого литерала.
        """
        for clause in self.clauses:
            if not clause: continue
            # Сортируем по абсолютному значению индекса
            sorted_lits = sorted(clause, key=lambda l: abs(l))
            lead_lit = sorted_lits[0]
            idx = abs(lead_lit)
            
            # Остаток дизъюнкта: (L2 v L3 ...)
            rest_bdd = self.bdd.false
            for lit in sorted_lits[1:]:
                var_name = f'x{abs(lit)}'
                node = self.bdd.add_expr(var_name if lit > 0 else f'~{var_name}')
                rest_bdd |= node
            
            # Если lead_lit=1, то при xi=0 должен выполняться rest_bdd
            # Если lead_lit=-1, то при xi=1 должен выполняться rest_bdd
            if lead_lit > 0:
                self.f_neg[idx] &= rest_bdd
            else:
                self.f_pos[idx] &= rest_bdd

    def solve(self):
        start_time = time.time()
        print(f"--- PQ-Functional Vacuum Start (N={self.n}, Clauses={len(self.clauses)}) ---")
        
        # Residue - это "накопитель будущего". В начале он пуст (True)
        residue = self.bdd.true

        # Идем СПРАВА НАЛЕВО (от n до 1)
        for i in range(self.n, 0, -1):
            var_name = f'x{i}'
            
            # 1. Анализируем текущую переменную xi через Residue (будущее)
            # Вычисляем условия "принуждения" (forced conditions)
            # must_be_0: условия, при которых xi=1 невозможно
            must_be_0 = ~self.bdd.exist([var_name], residue & self.bdd.add_expr(var_name))
            # must_be_1: условия, при которых xi=0 невозможно
            must_be_1 = ~self.bdd.exist([var_name], residue & self.bdd.add_expr(f"~{var_name}"))

            # Проверка на немедленный UNSAT (если будущее блокирует оба значения xi)
            if (must_be_0 & must_be_1) != self.bdd.false:
                # Если пересечение запретов дает True в какой-то области - там тупик
                # Если это константа True - всё, UNSAT
                if (must_be_0 & must_be_1) == self.bdd.true:
                    return "UNSAT"

            # 2. ТВОЙ ПРИКОЛ: Перемещение зависимости (Functional Link)
            # Мы обновляем Residue, вбирая в него функции xi
            # Residue_new = exists xi [ Residue_old & ( (xi & f_pos[i]) | (~xi & f_neg[i]) ) ]
            current_constraints = (self.bdd.add_expr(var_name) & self.f_pos[i]) | \
                                  (self.bdd.add_expr(f"~{var_name}") & self.f_neg[i])
            
            residue &= current_constraints
            
            # Элиминируем xi из Residue. Теперь Residue зависит только от переменных < i
            residue = self.bdd.exist([var_name], residue)

            # 3. ПРОБРОС ВЛЕВО: Обновляем все функции Pj (j < i)
            # Мы подмешиваем текущий Residue в функции "прошлого", 
            # чтобы они заранее знали об ограничениях, которые наложила xi
            if len(residue) > 1: # Оптимизация: если residue не True/False
                for j in range(1, i):
                    # Если функции Pj содержали xi, они уже упрощены (xi элиминирована),
                    # но теперь мы добавляем к ним "эхо" от xi через Residue.
                    self.f_pos[j] &= residue
                    self.f_neg[j] &= residue

            if i % 10 == 0 or i <= 5:
                print(f"Step {i:3} | BDD Nodes: {len(residue):5} | Elapsed: {time.time()-start_time:.2f}s")

        return "SAT"

def parse_dimacs(content):
    clauses = []
    vars_count = 0
    for line in content.splitlines():
        line = line.strip()
        if line.startswith('p cnf'):
            parts = line.split()
            vars_count = int(parts[2])
        elif line and not line.startswith('c'):
            lits = [int(x) for x in line.split() if x != '0']
            if lits: clauses.append(lits)
    return vars_count, clauses

if __name__ == "__main__":
    # Тестовый пример: (x1 v x2) & (~x1 v ~x2) -> SAT
    # Можно заменить на чтение файла: 
    # with open("path_to.cnf", "r") as f: content = f.read()
    test_cnf = """
    p cnf 3 3
    1 2 0
    -1 -2 0
    2 3 0
    """
    n_vars, clauses = parse_dimacs(test_cnf)
    solver = PQFunctionalVacuum(n_vars, clauses)
    result = solver.solve()
    print(f"\nFINAL RESULT: {result}")
