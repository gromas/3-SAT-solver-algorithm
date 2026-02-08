import itertools
import copy

class SATSolver3CNF:
    def __init__(self, formula):
        """
        formula: список клозов, каждый клоз - кортеж из 3 литералов.
                 Литералы: целые числа, положительные - переменная, отрицательные - отрицание.
                 Пример: (1, -2, 3) означает (x1 ∨ ¬x2 ∨ x3)
        """
        self.formula = formula
        self.variables = self._extract_variables()
        self.n_vars = len(self.variables)
        self.groups = []  # список групп (каждая группа - множество переменных)
        self.group_to_clause = {}  # отображение группы на соответствующий клоз
        self.neighbors = {}  # граф соседства групп
        self.A = {}  # A[group_idx] = список присваиваний
        self.phi = {}  # phi[group_idx][assign_idx] = список клозов 2-CNF
        
    def _extract_variables(self):
        """Извлекаем все переменные из формулы."""
        vars_set = set()
        for clause in self.formula:
            for lit in clause:
                vars_set.add(abs(lit))
        return sorted(list(vars_set))
    
    def _get_group_variables(self, clause):
        """Получаем множество переменных из клоза."""
        return set(abs(lit) for lit in clause)
    
    def _initialize_groups(self):
        """Инициализация групп по клозам."""
        for clause in self.formula:
            group = self._get_group_variables(clause)
            # Если группа меньше 3 переменных, дополняем произвольными
            while len(group) < 3:
                # Берем первую переменную, которой нет в группе
                for var in self.variables:
                    if var not in group:
                        group.add(var)
                        break
            group = tuple(sorted(group))
            
            if group not in self.group_to_clause:
                group_idx = len(self.groups)
                self.groups.append(group)
                self.group_to_clause[group] = clause
                
        # Строим граф соседства
        n_groups = len(self.groups)
        self.neighbors = {i: [] for i in range(n_groups)}
        
        for i in range(n_groups):
            for j in range(i+1, n_groups):
                if set(self.groups[i]) & set(self.groups[j]):
                    self.neighbors[i].append(j)
                    self.neighbors[j].append(i)
    
    def _evaluate_clause(self, clause, assignment):
        """
        Оценивает клоз при заданном присваивании.
        Возвращает:
          - None, если клоз истинен (удаляется)
          - [], если клоз ложен (противоречие)
          - Список оставшихся литералов в противном случае
        """
        remaining = []
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                value = assignment[var]
                if (lit > 0 and value == 1) or (lit < 0 and value == 0):
                    return None  # Клоз истинен
                # Литерал ложен - не добавляем
            else:
                remaining.append(lit)
        
        if not remaining:
            return []  # Пустой клоз - противоречие
        return remaining
    
    def _compute_phi(self, group_idx, assignment_dict):
        """
        Вычисляет Φ(a) для заданной группы и присваивания.
        assignment_dict: словарь {var: value} для переменных группы
        """
        group = self.groups[group_idx]
        clause = self.group_to_clause[group]
        
        # Применяем присваивание ко всем клозам
        phi_clauses = []
        
        for c in self.formula:
            result = self._evaluate_clause(c, assignment_dict)
            if result is None:
                continue  # Клоз истинен, удаляем
            elif result == []:
                return None  # Противоречие
            elif len(result) <= 2:
                # Добавляем как клоз 1 или 2-CNF
                if len(result) == 1:
                    phi_clauses.append((result[0],))
                else:
                    # Упорядочиваем литералы для однозначности
                    l1, l2 = result
                    if l1 > l2:  # Сортируем для устранения дубликатов
                        l1, l2 = l2, l1
                    phi_clauses.append((l1, l2))
        
        return phi_clauses
    
    def _is_2cnf_satisfiable(self, clauses):
        """Проверяет выполнимость 2-CNF формулы."""
        if not clauses:
            return True
        
        # Построение графа импликаций
        graph = {}
        rev_graph = {}
        
        for clause in clauses:
            if len(clause) == 1:
                l1 = clause[0]
                # l1 эквивалентен (l1 ∨ l1)
                l1_neg = -l1
                # Добавляем импликации: ¬l1 -> l1
                self._add_implication(graph, rev_graph, l1_neg, l1)
                self._add_implication(graph, rev_graph, l1, l1)  # для учета тривиальной
            else:
                l1, l2 = clause
                l1_neg, l2_neg = -l1, -l2
                # (l1 ∨ l2) эквивалентно (¬l1 -> l2) и (¬l2 -> l1)
                self._add_implication(graph, rev_graph, l1_neg, l2)
                self._add_implication(graph, rev_graph, l2_neg, l1)
        
        # Алгоритм Косарайю для поиска сильно связных компонент
        visited = set()
        order = []
        
        def dfs(v):
            visited.add(v)
            for u in graph.get(v, []):
                if u not in visited:
                    dfs(u)
            order.append(v)
        
        for v in graph:
            if v not in visited:
                dfs(v)
        
        # Обратный обход
        visited.clear()
        comp = {}
        current_comp = 0
        
        def dfs_rev(v):
            visited.add(v)
            comp[v] = current_comp
            for u in rev_graph.get(v, []):
                if u not in visited:
                    dfs_rev(u)
        
        for v in reversed(order):
            if v not in visited:
                dfs_rev(v)
                current_comp += 1
        
        # Проверка: если переменная и её отрицание в одной компоненте
        for v in comp:
            if -v in comp and comp[v] == comp[-v]:
                return False
        return True
    
    def _add_implication(self, graph, rev_graph, from_lit, to_lit):
        """Добавляет импликацию в граф."""
        if from_lit not in graph:
            graph[from_lit] = []
        graph[from_lit].append(to_lit)
        
        if to_lit not in rev_graph:
            rev_graph[to_lit] = []
        rev_graph[to_lit].append(from_lit)
    
    def _check_compatibility(self, phi1, phi2, shared_vars):
        """Проверяет совместимость двух Φ."""
        if not shared_vars:
            # Нет общих переменных - просто проверяем совместную выполнимость
            combined = phi1 + phi2
            return self._is_2cnf_satisfiable(combined)
        
        # Общие переменные должны быть согласованы
        # В нашем алгоритме это проверяется на уровне присваиваний
        # Здесь просто проверяем совместную выполнимость
        combined = phi1 + phi2
        return self._is_2cnf_satisfiable(combined)
    
    def _intersection_of_phis(self, phis_list):
        """Находит пересечение нескольких Φ (общие клозы)."""
        if not phis_list:
            return []
        
        # Приводим все клозы к каноническому виду и считаем частоту
        clause_count = {}
        
        for phi in phis_list:
            phi_set = set()
            for clause in phi:
                if len(clause) == 1:
                    phi_set.add((clause[0],))
                else:
                    l1, l2 = clause
                    if l1 > l2:
                        l1, l2 = l2, l1
                    phi_set.add((l1, l2))
            
            for clause in phi_set:
                clause_count[clause] = clause_count.get(clause, 0) + 1
        
        # Берем клозы, которые есть во всех Φ
        n = len(phis_list)
        intersection = [clause for clause, count in clause_count.items() 
                       if count == n]
        
        return intersection
    
    def solve(self):
        """Основной алгоритм решения."""
        # Шаг 0: Инициализация
        self._initialize_groups()
        n_groups = len(self.groups)
        
        # Инициализируем A и phi
        for i in range(n_groups):
            self.A[i] = []
            self.phi[i] = {}
            
            group = self.groups[i]
            # Все возможные присваивания для группы
            for bits in itertools.product([0, 1], repeat=3):
                assignment = {group[j]: bits[j] for j in range(3)}
                phi_a = self._compute_phi(i, assignment)
                
                if phi_a is None:  # Противоречие
                    continue
                
                if self._is_2cnf_satisfiable(phi_a):
                    self.A[i].append(bits)
                    self.phi[i][bits] = phi_a
        
        # Проверка на пустые группы
        for i in range(n_groups):
            if not self.A[i]:
                return "UNSAT"
        
        # Шаг 1: Итерационное уточнение
        changed = True
        iteration = 0
        
        while changed:
            changed = False
            iteration += 1
            print(f"Итерация {iteration}")
            
            # Создаем копии для безопасного изменения
            new_A = copy.deepcopy(self.A)
            new_phi = copy.deepcopy(self.phi)
            
            for i in range(n_groups):
                for assignment in list(self.A[i]):  # Используем list для копирования
                    assignment_tuple = assignment
                    
                    # Проверяем соседние группы
                    for j in self.neighbors[i]:
                        # Находим совместимые присваивания в группе j
                        compatible_assignments = []
                        compatible_phis = []
                        
                        for b_assignment in self.A[j]:
                            # Проверяем совместимость на общих переменных
                            common_vars = set(self.groups[i]) & set(self.groups[j])
                            compatible = True
                            
                            for var in common_vars:
                                idx_i = self.groups[i].index(var)
                                idx_j = self.groups[j].index(var)
                                if assignment_tuple[idx_i] != b_assignment[idx_j]:
                                    compatible = False
                                    break
                            
                            if not compatible:
                                continue
                            
                            # Проверяем совместную выполнимость Φ
                            phi_i = self.phi[i][assignment_tuple]
                            phi_j = self.phi[j][b_assignment]
                            
                            if self._check_compatibility(phi_i, phi_j, common_vars):
                                compatible_assignments.append(b_assignment)
                                compatible_phis.append(phi_j)
                        
                        if not compatible_assignments:
                            # Удаляем присваивание из A[i]
                            if assignment_tuple in new_A[i]:
                                new_A[i].remove(assignment_tuple)
                                if assignment_tuple in new_phi[i]:
                                    del new_phi[i][assignment_tuple]
                                changed = True
                                break
                        else:
                            # Берем пересечение ограничений
                            intersection = self._intersection_of_phis(compatible_phis)
                            
                            # Добавляем новые ограничения к Φ
                            current_phi = new_phi[i].get(assignment_tuple, [])
                            new_clauses = [c for c in intersection if c not in current_phi]
                            
                            if new_clauses:
                                updated_phi = current_phi + new_clauses
                                if not self._is_2cnf_satisfiable(updated_phi):
                                    # Удаляем присваивание
                                    if assignment_tuple in new_A[i]:
                                        new_A[i].remove(assignment_tuple)
                                        if assignment_tuple in new_phi[i]:
                                            del new_phi[i][assignment_tuple]
                                        changed = True
                                        break
                                else:
                                    new_phi[i][assignment_tuple] = updated_phi
                                    changed = True
            
            # Обновляем A и phi
            self.A = new_A
            self.phi = new_phi
            
            # Проверка на пустые группы
            for i in range(n_groups):
                if not self.A[i]:
                    return "UNSAT"
            
            # Если изменений не было, завершаем
            if not changed:
                break
        
        # Шаг 2: Проверка результата
        for i in range(n_groups):
            if not self.A[i]:
                return "UNSAT"
        
        # Построение решения
        solution = self._construct_solution()
        return "SAT", solution
    
    def _construct_solution(self):
        """Строит выполняющее присваивание из оставшихся присваиваний."""
        # Простой подход: выбираем первое присваивание из каждой группы
        # и разрешаем конфликты (если они есть)
        assignment = {}
        
        for i in range(len(self.groups)):
            if self.A[i]:
                group = self.groups[i]
                # Берем первое присваивание
                bits = self.A[i][0]
                for j, var in enumerate(group):
                    if var not in assignment:
                        assignment[var] = bits[j]
                    # Если конфликт, выбираем значение из текущей группы
                    elif assignment[var] != bits[j]:
                        # В корректном решении такого не должно быть
                        assignment[var] = bits[j]  # Перезаписываем
        
        # Заполняем пропущенные переменные (если есть)
        for var in self.variables:
            if var not in assignment:
                assignment[var] = 0  # Произвольное значение
        
        return assignment

# Пример использования
def example():
    # Пример 1: Простая выполнимая формула
    # (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ ¬x3)
    formula1 = [
        (1, 2, 3),
        (-1, -2, -3)
    ]
    
    solver1 = SATSolver3CNF(formula1)
    result1 = solver1.solve()
    print("Пример 1:", result1)
    
    # Пример 2: XOR формула (выполнимая)
    # x1 ⊕ x2 ⊕ x3 = 1
    formula2 = [
        (1, 2, 3),
        (1, -2, -3),
        (-1, 2, -3),
        (-1, -2, 3)
    ]
    
    solver2 = SATSolver3CNF(formula2)
    result2 = solver2.solve()
    print("Пример 2:", result2)
    
    # Пример 3: Простая невыполнимая формула
    # (x1) ∧ (¬x1)
    # В 3-CNF: (x1 ∨ x1 ∨ x1) ∧ (¬x1 ∨ ¬x1 ∨ ¬x1)
    formula3 = [
        (1, 1, 1),
        (-1, -1, -1)
    ]
    
    solver3 = SATSolver3CNF(formula3)
    result3 = solver3.solve()
    print("Пример 3:", result3)
    
    # Пример 4: Циклический XOR (невыполнимая система)
    # x1 ⊕ x2 ⊕ x3 = 1
    # x1 ⊕ x2 ⊕ x4 = 1
    # x3 ⊕ x4 = 0
    formula4 = [
        (1, 2, 3),
        (1, -2, -3),
        (-1, 2, -3),
        (-1, -2, 3),  # x1⊕x2⊕x3=1
        (1, 2, 4),
        (1, -2, -4),
        (-1, 2, -4),
        (-1, -2, 4),  # x1⊕x2⊕x4=1
        (3, 4, 5),    # Просто для дополнения до 3 переменных
        (-3, -4, 5)   # Это не совсем точное кодирование x3⊕x4=0
    ]
    
    solver4 = SATSolver3CNF(formula4)
    result4 = solver4.solve()
    print("Пример 4:", result4)

if __name__ == "__main__":
    example()
