import sys
from dd.autoref import BDD

class PQProximitySolver:
    def __init__(self, vars_count, clauses):
        self.n = vars_count
        self.clauses = clauses
        self.bdd_manager = BDD()
        for i in range(1, self.n + 1):
            self.bdd_manager.declare(f'x{i}')
        
        self.f_pos = {i: self.bdd_manager.true for i in range(1, self.n + 1)}
        self.f_neg = {i: self.bdd_manager.true for i in range(1, self.n + 1)}
        self._build_initial_functions()

    def _build_initial_functions(self):
        for clause in self.clauses:
            sorted_lits = sorted(clause, key=lambda l: abs(l))
            idx = abs(sorted_lits[0])
            rest_bdd = self.bdd_manager.false
            for lit in sorted_lits[1:]:
                v_name = f'x{abs(lit)}'
                node = self.bdd_manager.add_expr(v_name if lit > 0 else f'~{v_name}')
                rest_bdd |= node
            
            if sorted_lits[0] > 0:
                self.f_neg[idx] &= rest_bdd
            else:
                self.f_pos[idx] &= rest_bdd

    def solve(self):
        print(f"--- Запуск Proximity-Vacuum (N={self.n}) ---")
        residue = self.bdd_manager.true

        for i in range(self.n, 0, -1):
            # 1. Проверяем допустимость через текущий Residue
            # Мы смотрим, не блокирует ли "будущее" (справа) текущую xi
            can_be_true = (residue & self.bdd_manager.add_expr(f'x{i}')) != self.bdd_manager.false
            can_be_false = (residue & self.bdd_manager.add_expr(f'~x{i}')) != self.bdd_manager.false

            if not can_be_true and not can_be_false:
                return "UNSAT"

            # 2. Выбираем значение (асимметрично)
            # Приоритет отдаем тому значению, которое "свободно"
            fixed_val = True if can_be_true else False

            # 3. ТОТ САМЫЙ "ПРИКОЛ": Прокси-связь (Wormhole)
            # Вместо того чтобы вливать f_pos[i] или f_neg[i] как BDD-объекты, 
            # мы связываем xi с переменными, которые стоят в этих функциях.
            
            current_target_function = self.f_pos[i] if fixed_val else self.f_neg[i]
            
            # Мы "абстрагируем" текущую переменную: 
            # Residue теперь хранит: "Если xi была выбрана, то ее последствия (функция) 
            # должны быть выполнены". 
            # Но мы не вскрываем функцию, мы просто накладываем конъюнкцию.
            residue &= current_target_function
            
            # 4. РАСПРОСТРАНЕНИЕ (Propagation) влево
            # Мы упрощаем функции PJ, зная что xi теперь константа
            for j in range(1, i):
                self.f_pos[j] = self.f_pos[j].let({f'x{i}': fixed_val})
                self.f_neg[j] = self.f_neg[j].let({f'x{i}': fixed_val})

            # 5. Элиминация (Схлопывание измерения)
            # Так как мы подставили fixed_val в функции слева, 
            # xi теперь "выпаривается" из системы.
            residue = self.bdd_manager.exist([f'x{i}'], residue)

            if i % 10 == 0 or i < 5:
                print(f"Шаг {i} | BDD size: {len(residue)} | x{i} -> {fixed_val}")

        return "SAT"

# Код для загрузки и запуска (идентичен прошлому)
# ... [parser] ...

if __name__ == "__main__":
    # Сюда можно подставить путь к DIMACS из твоего репозитория
    # n, cls = parse_dimacs_file("uf100-03.cnf")
    # solver = PQProximitySolver(n, cls)
    # print(solver.solve())
    pass
