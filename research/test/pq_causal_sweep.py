"""
Модуль с реализацией SAT решателя на основе P/Q алгоритма с расщеплением
"""

class BDDNode:
    """Узел BDD для представления булевой функции"""
    
    def __init__(self, value=None):
        """
        Инициализация узла BDD
        
        Args:
            value: может быть bool (True/False) или словарем для внутреннего узла
        """
        if isinstance(value, bool) or value is None:
            # Листовой узел (True/False) или пустой
            self.is_leaf = True
            self.value = value
            self.var = None
            self.then_branch = None
            self.else_branch = None
        elif isinstance(value, dict):
            # Внутренний узел
            self.is_leaf = False
            self.var = value.get('var')
            self.then_branch = value.get('then')
            self.else_branch = value.get('else')
            self.value = None
    
    @staticmethod
    def true():
        """Создать узел True"""
        return BDDNode(True)
    
    @staticmethod
    def false():
        """Создать узел False"""
        return BDDNode(False)
    
    @staticmethod
    def from_clause(clause, var_mapping=None):
        """
        Создать BDD из дизъюнкта (клоза)
        
        Args:
            clause: список литералов [1, -2, 3]
            var_mapping: отображение переменных (не обязательно)
        """
        if not clause:
            return BDDNode.false()
        
        # Для простоты представляем дизъюнкт как (lit1 OR lit2 OR ...)
        # Строим как дерево решений
        if var_mapping is None:
            var_mapping = {}
        
        # Сортируем литералы по абсолютному значению
        literals = sorted(clause, key=lambda x: abs(x))
        
        return BDDNode._build_or_tree(literals, 0)
    
    @staticmethod
    def _build_or_tree(literals, idx):
        """Построить дерево OR для списка литералов"""
        if idx >= len(literals):
            return BDDNode.false()
        
        lit = literals[idx]
        var = abs(lit)
        is_positive = lit > 0
        
        # Строим: (literal) OR (остаток)
        # literal - это условие: если var=True (для положительного) или var=False (для отрицательного)
        rest = BDDNode._build_or_tree(literals, idx + 1)
        
        if is_positive:
            # Если переменная True -> клоз выполнен (True)
            # Если переменная False -> проверяем остаток
            return BDDNode({
                'var': var,
                'then': BDDNode.true(),
                'else': rest
            })
        else:
            # Если переменная False -> клоз выполнен (True)
            # Если переменная True -> проверяем остаток
            return BDDNode({
                'var': var,
                'then': rest,
                'else': BDDNode.true()
            })
    
    def assign(self, var, value):
        """
        Подстановка значения переменной
        
        Args:
            var: номер переменной
            value: значение (True/False)
        
        Returns:
            новый BDD после подстановки
        """
        if self.is_leaf:
            return self
        
        if self.var == var:
            # Заменяем на соответствующую ветку
            if value:
                return self.then_branch
            else:
                return self.else_branch
        elif self.var < var:
            # Текущая переменная меньше, рекурсивно применяем к веткам
            new_then = self.then_branch.assign(var, value)
            new_else = self.else_branch.assign(var, value)
            
            # Если ветки одинаковые, возвращаем одну из них
            if new_then.is_leaf and new_else.is_leaf and new_then.value == new_else.value:
                return new_then
            
            return BDDNode({
                'var': self.var,
                'then': new_then,
                'else': new_else
            })
        else:
            # Текущая переменная больше, подстановка не влияет
            return self
    
    def exist(self, var):
        """
        Квантор существования: существует ли значение var, при котором функция истинна
        
        Args:
            var: номер переменной
        
        Returns:
            новый BDD после применения квантора существования
        """
        if self.is_leaf:
            return self
        
        if self.var == var:
            # exist = then OR else
            return BDDNode._or(self.then_branch, self.else_branch)
        elif self.var < var:
            # Текущая переменная меньше, рекурсивно применяем к веткам
            new_then = self.then_branch.exist(var)
            new_else = self.else_branch.exist(var)
            
            # Если ветки одинаковые, возвращаем одну из них
            if new_then.is_leaf and new_else.is_leaf and new_then.value == new_else.value:
                return new_then
            
            return BDDNode({
                'var': self.var,
                'then': new_then,
                'else': new_else
            })
        else:
            # Текущая переменная больше, квантор не влияет
            return self
    
    def __and__(self, other):
        """Логическое И (конъюнкция)"""
        return BDDNode._and(self, other)
    
    def __or__(self, other):
        """Логическое ИЛИ (дизъюнкция)"""
        return BDDNode._or(self, other)
    
    @staticmethod
    def _and(a, b):
        """Конъюнкция двух BDD"""
        # Базовые случаи
        if a.is_leaf and a.value is False:
            return BDDNode.false()
        if b.is_leaf and b.value is False:
            return BDDNode.false()
        if a.is_leaf and a.value is True:
            return b
        if b.is_leaf and b.value is True:
            return a
        
        # Если оба листовые и True
        if a.is_leaf and b.is_leaf and a.value is True and b.value is True:
            return BDDNode.true()
        
        # Определяем переменную с минимальным номером
        if a.is_leaf:
            var = b.var
            a_then = a
            a_else = a
            b_then = b.then_branch
            b_else = b.else_branch
        elif b.is_leaf:
            var = a.var
            a_then = a.then_branch
            a_else = a.else_branch
            b_then = b
            b_else = b
        else:
            var = min(a.var, b.var)
            if a.var == var:
                a_then = a.then_branch
                a_else = a.else_branch
            else:
                a_then = a
                a_else = a
            
            if b.var == var:
                b_then = b.then_branch
                b_else = b.else_branch
            else:
                b_then = b
                b_else = b
        
        # Рекурсивно строим результат
        then_branch = BDDNode._and(a_then, b_then)
        else_branch = BDDNode._and(a_else, b_else)
        
        # Оптимизация: если ветки одинаковые, возвращаем одну
        if then_branch.is_leaf and else_branch.is_leaf and then_branch.value == else_branch.value:
            return then_branch
        
        return BDDNode({
            'var': var,
            'then': then_branch,
            'else': else_branch
        })
    
    @staticmethod
    def _or(a, b):
        """Дизъюнкция двух BDD"""
        # Базовые случаи
        if a.is_leaf and a.value is True:
            return BDDNode.true()
        if b.is_leaf and b.value is True:
            return BDDNode.true()
        if a.is_leaf and a.value is False:
            return b
        if b.is_leaf and b.value is False:
            return a
        
        # Если оба листовые и False
        if a.is_leaf and b.is_leaf and a.value is False and b.value is False:
            return BDDNode.false()
        
        # Определяем переменную с минимальным номером
        if a.is_leaf:
            var = b.var
            a_then = a
            a_else = a
            b_then = b.then_branch
            b_else = b.else_branch
        elif b.is_leaf:
            var = a.var
            a_then = a.then_branch
            a_else = a.else_branch
            b_then = b
            b_else = b
        else:
            var = min(a.var, b.var)
            if a.var == var:
                a_then = a.then_branch
                a_else = a.else_branch
            else:
                a_then = a
                a_else = a
            
            if b.var == var:
                b_then = b.then_branch
                b_else = b.else_branch
            else:
                b_then = b
                b_else = b
        
        # Рекурсивно строим результат
        then_branch = BDDNode._or(a_then, b_then)
        else_branch = BDDNode._or(a_else, b_else)
        
        # Оптимизация: если ветки одинаковые, возвращаем одну
        if then_branch.is_leaf and else_branch.is_leaf and then_branch.value == else_branch.value:
            return then_branch
        
        return BDDNode({
            'var': var,
            'then': then_branch,
            'else': else_branch
        })
    
    def __eq__(self, other):
        """Сравнение двух BDD"""
        if self.is_leaf and other.is_leaf:
            return self.value == other.value
        if self.is_leaf or other.is_leaf:
            return False
        
        return (self.var == other.var and 
                self.then_branch == other.then_branch and 
                self.else_branch == other.else_branch)
    
    def __repr__(self):
        """Строковое представление"""
        if self.is_leaf:
            if self.value is True:
                return "True"
            elif self.value is False:
                return "False"
            else:
                return "None"
        else:
            return f"BDD(x{self.var}, then={self.then_branch}, else={self.else_branch})"


class SATSolver:
    """
    SAT решатель на основе P/Q алгоритма с расщеплением
    
    Алгоритм:
    1. Инициализация: для каждой переменной создаем pos и neg BDD
    2. Загрузка: распределяем клозы по переменным
    3. Расчет: обратный проход с применением кванторов существования
    """
    
    def __init__(self, clauses, n_vars):
        """
        Инициализация решателя
        
        Args:
            clauses: список клозов (каждый клоз - список литералов)
            n_vars: количество переменных
        """
        self.clauses = clauses
        self.n_vars = n_vars
        
        # Результат решения
        self.assignment = {}
        self.is_sat = None
    
    def solve(self):
        """
        Запуск алгоритма решения
        
        Returns:
            bool: True если формула выполнима, False если невыполнима
        """
        print("\n" + "="*60)
        print("ЗАПУСК P/Q SAT РЕШАТЕЛЯ")
        print("="*60)
        
        # Шаг 1: Инициализация
        print("\n[1] ИНИЦИАЛИЗАЦИЯ")
        pos = [None] * (self.n_vars + 1)  # индексация с 1
        neg = [None] * (self.n_vars + 1)
        
        for i in range(1, self.n_vars + 1):
            pos[i] = BDDNode.true()
            neg[i] = BDDNode.true()
            print(f"  pos[{i}] = True, neg[{i}] = True")
        
        # Шаг 2: Загрузка функций
        print("\n[2] ЗАГРУЗКА ФУНКЦИЙ")
        
        # Копируем клозы для обработки
        remaining_clauses = self.clauses.copy()
        
        for i in range(1, self.n_vars + 1):
            if not remaining_clauses:
                print(f"  Все клозы обработаны на переменной x{i}")
                break
            
            print(f"\n  --- Переменная x{i} ---")
            
            # Выбираем все клозы, содержащие литералы переменной i
            clauses_for_xi = []
            clauses_to_remove = []
            
            for j, clause in enumerate(remaining_clauses):
                if any(abs(lit) == i for lit in clause):
                    clauses_for_xi.append(clause)
                    clauses_to_remove.append(j)
            
            # Удаляем выбранные клозы (в обратном порядке)
            for j in reversed(clauses_to_remove):
                remaining_clauses.pop(j)
            
            print(f"  Выбрано {len(clauses_for_xi)} клозов для x{i}")
            if clauses_for_xi:
                print(f"  Клозы: {clauses_for_xi}")
            
            # Если есть клозы для этой переменной
            if clauses_for_xi:
                # Строим конъюнкцию всех клозов для этой переменной
                clause_bdd = BDDNode.true()
                for clause in clauses_for_xi:
                    clause_bdd = clause_bdd & BDDNode.from_clause(clause)
                
                print(f"  Построен BDD для клозов: {clause_bdd}")
                
                # Обновляем pos и neg
                pos[i] = (pos[i] & clause_bdd).assign(i, False)
                neg[i] = (neg[i] & clause_bdd).assign(i, True)
                
                print(f"  pos[{i}] после подстановки True: {pos[i]}")
                print(f"  neg[{i}] после подстановки False: {neg[i]}")
        
        # Шаг 3: Расчет (обратный проход)
        print("\n[3] ОБРАТНЫЙ ПРОХОД")
        
        for i in range(self.n_vars, 0, -1):
            print(f"\n  --- Переменная x{i} ---")
            print(f"    pos[{i}] = {pos[i]}")
            print(f"    neg[{i}] = {neg[i]}")
            
            # Проверка на противоречие
            if (pos[i].is_leaf and pos[i].value is False and 
                neg[i].is_leaf and neg[i].value is False):
                print(f"    ✗ Противоречие: и pos и neg = False")
                self.is_sat = False
                return False
            
            # Если обе ветки возможны (True)
            if (pos[i].is_leaf and pos[i].value is True and 
                neg[i].is_leaf and neg[i].value is True):
                print(f"    Обе ветки возможны (True), применяем квантор существования")
                
                # Применяем квантор существования ко всем предыдущим переменным
                for j in range(1, i):
                    if pos[j] is not None and not (pos[j].is_leaf and pos[j].value is True):
                        pos[j] = pos[j].exist(i)
                    if neg[j] is not None and not (neg[j].is_leaf and neg[j].value is True):
                        neg[j] = neg[j].exist(i)
                
                print(f"    После квантора существования:")
                for j in range(1, i):
                    if pos[j] is not None:
                        print(f"      pos[{j}] = {pos[j]}")
                    if neg[j] is not None:
                        print(f"      neg[{j}] = {neg[j]}")
            else:
                # Определяем значение переменной
                if pos[i].is_leaf and pos[i].value is True and neg[i].is_leaf and neg[i].value is False:
                    xi_val = True
                    print(f"    Только pos = True -> x{i} = True")
                elif pos[i].is_leaf and pos[i].value is False and neg[i].is_leaf and neg[i].value is True:
                    xi_val = False
                    print(f"    Только neg = True -> x{i} = False")
                else:
                    # Сложный случай - нужно вычислить значение
                    # Для простоты выбираем True, если pos не False
                    if not (pos[i].is_leaf and pos[i].value is False):
                        xi_val = True
                        print(f"    pos не False -> x{i} = True (упрощенно)")
                    else:
                        xi_val = False
                        print(f"    neg не False -> x{i} = False (упрощенно)")
                
                self.assignment[i] = xi_val
                
                # Применяем подстановку ко всем предыдущим переменным
                for j in range(1, i):
                    if pos[j] is not None:
                        pos[j] = pos[j].assign(i, xi_val)
                    if neg[j] is not None:
                        neg[j] = neg[j].assign(i, xi_val)
                
                print(f"    После подстановки x{i}={xi_val}:")
                for j in range(1, i):
                    if pos[j] is not None:
                        print(f"      pos[{j}] = {pos[j]}")
                    if neg[j] is not None:
                        print(f"      neg[{j}] = {neg[j]}")
        
        # Шаг 4: Проверка решения
        print("\n[4] ПРОВЕРКА РЕШЕНИЯ")
        
        if pos[1] is not None and neg[1] is not None:
            if (pos[1].is_leaf and pos[1].value is False and 
                neg[1].is_leaf and neg[1].value is False):
                print("  ✗ Противоречие для x1: UNSAT")
                self.is_sat = False
                return False
        
        # Если дошли до конца - формула выполнима
        print("  ✓ Формула выполнима (SAT)")
        
        # Дополняем недостающие значения переменных
        for i in range(1, self.n_vars + 1):
            if i not in self.assignment:
                # Если переменная не определена, выбираем произвольное значение
                self.assignment[i] = True
        
        print(f"\nНайденное решение: {self.assignment}")
        
        self.is_sat = True
        return True
    
    def get_assignment(self):
        """
        Получить найденное решение
        
        Returns:
            dict: словарь {переменная: значение}
        """
        return self.assignment


# Для тестирования
def test_solver():
    """Тестирование решателя"""
    print("\n" + "="*70)
    print("ТЕСТИРОВАНИЕ SAT РЕШАТЕЛЯ")
    print("="*70)
    
    # Тест 1: Простая выполнимая формула
    print("\nТЕСТ 1: Простая выполнимая формула")
    clauses1 = [
        [1, 2],    # x1 OR x2
        [-1, 2],   # not x1 OR x2
        [1, -2]    # x1 OR not x2
    ]
    
    solver1 = SATSolver(clauses1, 2)
    result1 = solver1.solve()
    print(f"\nРезультат: {'SAT' if result1 else 'UNSAT'}")
    if result1:
        print(f"Решение: {solver1.get_assignment()}")
    
    # Тест 2: Невыполнимая формула
    print("\nТЕСТ 2: Невыполнимая формула")
    clauses2 = [
        [1],    # x1
        [-1]    # not x1
    ]
    
    solver2 = SATSolver(clauses2, 1)
    result2 = solver2.solve()
    print(f"\nРезультат: {'SAT' if result2 else 'UNSAT'}")
    
    # Тест 3: Формула из трех переменных
    print("\nТЕСТ 3: Формула с тремя переменными")
    clauses3 = [
        [1, 2, 3],
        [-1, -2],
        [2, -3]
    ]
    
    solver3 = SATSolver(clauses3, 3)
    result3 = solver3.solve()
    print(f"\nРезультат: {'SAT' if result3 else 'UNSAT'}")
    if result3:
        print(f"Решение: {solver3.get_assignment()}")


if __name__ == "__main__":
    test_solver()
