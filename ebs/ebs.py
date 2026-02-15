import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from collections import defaultdict, deque
import heapq
import hashlib
import time
from typing import List, Set, Dict, Tuple, Optional
import random
from dataclasses import dataclass, field
import math
from itertools import combinations

# ============================================================================
# Модуль 1: PQ-Planner (построение уровней элиминации)
# ============================================================================

class PQPlanner:
    """
    Построение порядка элиминации переменных на основе алгоритма PQSAT.
    Использует эвристику весов переменных для определения порядка.
    """
    
    def __init__(self, cnf_formula: List[Set[int]]):
        """
        Args:
            cnf_formula: список клозов, каждый клоз - множество литералов
                        (положительные и отрицательные числа)
        """
        self.cnf = cnf_formula
        self.vars = self._extract_vars()
        self.var_occurrences = self._count_occurrences()
        self.elimination_order = []
        
    def _extract_vars(self) -> Set[int]:
        """Извлечение всех переменных из формулы"""
        vars_set = set()
        for clause in self.cnf:
            for lit in clause:
                vars_set.add(abs(lit))
        return vars_set
    
    def _count_occurrences(self) -> Dict[int, int]:
        """Подсчет количества вхождений каждой переменной"""
        occurrences = defaultdict(int)
        for clause in self.cnf:
            for lit in clause:
                occurrences[abs(lit)] += 1
        return occurrences
    
    def compute_elimination_order(self) -> List[int]:
        """
        Вычисление порядка элиминации переменных справа налево.
        Использует приоритетную очередь с весом = occurrences * clause_size_factor
        """
        # Копируем формулу для манипуляций
        active_clauses = [set(clause) for clause in self.cnf]
        active_vars = set(self.vars)
        elimination_order = []
        
        # Приоритетная очередь: (вес, переменная)
        # Меньший вес = выше приоритет для элиминации
        pq = []
        
        # Инициализация весов
        var_weight = {}
        for var in active_vars:
            # Вес = количество вхождений * средний размер клозов с этой переменной
            occurrences = self.var_occurrences[var]
            clauses_with_var = [c for c in active_clauses if var in c or -var in c]
            avg_clause_size = sum(len(c) for c in clauses_with_var) / max(1, len(clauses_with_var))
            weight = occurrences * avg_clause_size
            var_weight[var] = weight
            heapq.heappush(pq, (weight, var))
        
        # Построение порядка элиминации
        while pq and active_vars:
            weight, var = heapq.heappop(pq)
            
            if var not in active_vars:
                continue
                
            # Добавляем переменную в порядок элиминации (справа налево)
            elimination_order.append(var)
            active_vars.remove(var)
            
            # Обновляем веса оставшихся переменных
            for other_var in active_vars:
                if other_var in var_weight:
                    clauses_with_var = [c for c in active_clauses 
                                      if other_var in c or -other_var in c]
                    if clauses_with_var:
                        avg_size = sum(len(c) for c in clauses_with_var) / len(clauses_with_var)
                        new_weight = len(clauses_with_var) * avg_size
                    else:
                        new_weight = 0
                    
                    if new_weight < var_weight[other_var]:
                        var_weight[other_var] = new_weight
                        heapq.heappush(pq, (new_weight, other_var))
        
        return list(reversed(elimination_order))


# ============================================================================
# Модуль 2: Viterbi Core (Beam Search с прямой проверкой клозов)
# ============================================================================

@dataclass
class BeamPath:
    """Представление пути в beam search"""
    assignment: np.ndarray  # битовый массив назначений (-1 для неопределенных)
    weight: float           # вес/невязка пути (количество невыполненных клозов)
    hash_id: str = field(init=False)
    
    def __post_init__(self):
        """Вычисление хеша для кэширования"""
        self.hash_id = hashlib.md5(self.assignment.tobytes()).hexdigest()
    
    def __lt__(self, other):
        return self.weight < other.weight


class ViterbiCore:
    """
    Ядро алгоритма Витерби с Beam Search.
    Ведет K путей, вычисляя невязку через прямую проверку клозов.
    """
    
    def __init__(self, cnf_formula: List[Set[int]], elimination_order: List[int], 
                 beam_size: int, diversity_lambda: float = 0.1):
        """
        Args:
            cnf_formula: формула в КНФ
            elimination_order: порядок элиминации переменных
            beam_size: размер луча
            diversity_lambda: коэффициент разнообразия
        """
        self.cnf = cnf_formula
        self.elimination_order = elimination_order
        self.beam_size = beam_size
        self.diversity_lambda = diversity_lambda
        
        # Маппинг переменных на индексы
        all_vars = set()
        for clause in cnf_formula:
            for lit in clause:
                all_vars.add(abs(lit))
        
        self.var_to_idx = {var: i for i, var in enumerate(sorted(all_vars))}
        self.idx_to_var = {i: var for var, i in self.var_to_idx.items()}
        self.num_vars = len(self.var_to_idx)
        
        # Представляем клозы в формате для быстрой проверки
        self.clauses = []
        for clause in cnf_formula:
            pos_lits = []
            neg_lits = []
            for lit in clause:
                var_idx = self.var_to_idx[abs(lit)]
                if lit > 0:
                    pos_lits.append(var_idx)
                else:
                    neg_lits.append(var_idx)
            self.clauses.append((pos_lits, neg_lits))
        
        # Кэш для хранения посещенных состояний
        self.state_cache = set()
        
        # Текущие пути
        self.paths = []
        
        # Статистика
        self.energy_history = []
        
    def initialize_paths(self):
        """Инициализация путей"""
        empty_assignment = np.full(self.num_vars, -1, dtype=np.int8)
        self.paths = [BeamPath(assignment=empty_assignment.copy(), weight=0.0)]
        self.state_cache.add(self.paths[0].hash_id)
    
    def check_clause_satisfied(self, assignment: np.ndarray, clause_idx: int) -> bool:
        """
        Проверка, выполнен ли клоз при данном назначении.
        Возвращает True, если клоз выполнен, False если не выполнен или не определен.
        """
        pos_lits, neg_lits = self.clauses[clause_idx]
        
        # Проверка положительных литералов
        for var_idx in pos_lits:
            if assignment[var_idx] == 1:
                return True  # Клоз выполнен
        
        # Проверка отрицательных литералов (переменная должна быть 0)
        for var_idx in neg_lits:
            if assignment[var_idx] == 0:
                return True  # Клоз выполнен
        
        # Если все переменные определены и ни один литерал не истинен, клоз не выполнен
        all_defined = True
        for var_idx in pos_lits + neg_lits:
            if assignment[var_idx] == -1:
                all_defined = False
                break
        
        if all_defined:
            return False  # Клоз не выполнен
        else:
            return True  # Считаем выполненным, если есть неопределенные переменные
    
    def count_unsatisfied_clauses(self, assignment: np.ndarray) -> int:
        """
        Подсчет количества явно невыполненных клозов.
        """
        unsatisfied = 0
        for i in range(len(self.clauses)):
            if not self.check_clause_satisfied(assignment, i):
                unsatisfied += 1
        return unsatisfied
    
    def compute_residual(self, assignment: np.ndarray) -> float:
        """
        Вычисление невязки (энергии конфликта) для назначения.
        """
        unsatisfied = self.count_unsatisfied_clauses(assignment)
        undefined_count = np.sum(assignment == -1)
        
        # Базовая энергия = количество невыполненных клозов
        residual = float(unsatisfied)
        
        # Добавляем небольшой штраф за неопределенные переменные
        if undefined_count > 0:
            residual += 0.1 * (undefined_count / self.num_vars)
        
        return residual
    
    def expand_path(self, path: BeamPath, var_idx: int) -> List[BeamPath]:
        """
        Расширение пути для переменной с индексом var_idx.
        """
        new_paths = []
        
        for value in [0, 1]:
            new_assignment = path.assignment.copy()
            new_assignment[var_idx] = value
            
            new_path = BeamPath(new_assignment, 0.0)
            if new_path.hash_id in self.state_cache:
                continue
            
            residual = self.compute_residual(new_assignment)
            diversity_penalty = self._compute_diversity_penalty(new_assignment)
            
            new_path.weight = residual + self.diversity_lambda * diversity_penalty
            new_paths.append(new_path)
            self.state_cache.add(new_path.hash_id)
        
        return new_paths
    
    def _compute_diversity_penalty(self, assignment: np.ndarray) -> float:
        """Штраф за схожесть с существующими путями"""
        if not self.paths:
            return 0.0
        
        max_similarity = 0.0
        for path in self.paths:
            defined_mask = (assignment != -1) & (path.assignment != -1)
            if np.any(defined_mask):
                similarity = np.mean(assignment[defined_mask] == path.assignment[defined_mask])
                max_similarity = max(max_similarity, similarity)
        
        return max_similarity
    
    def beam_search_step(self, var_idx: int) -> List[BeamPath]:
        """Один шаг beam search"""
        candidates = []
        
        for path in self.paths:
            new_paths = self.expand_path(path, var_idx)
            candidates.extend(new_paths)
        
        if not candidates:
            candidates = self.paths.copy()
        
        # Сортировка по весу
        candidates.sort(key=lambda p: p.weight)
        
        # Выбор top-K с учетом разнообразия
        selected = []
        for candidate in candidates:
            if len(selected) >= self.beam_size:
                break
            
            if self._is_diverse_enough(candidate, selected):
                selected.append(candidate)
        
        return selected
    
    def _is_diverse_enough(self, candidate: BeamPath, selected: List[BeamPath]) -> bool:
        """Проверка разнообразия"""
        if not selected:
            return True
        
        for sel in selected:
            defined_mask = (candidate.assignment != -1) & (sel.assignment != -1)
            if np.any(defined_mask):
                similarity = np.mean(candidate.assignment[defined_mask] == sel.assignment[defined_mask])
                if similarity > 0.9:  # Повысим порог схожести
                    return False
        return True
    
    def is_satisfying_assignment(self, assignment: np.ndarray) -> bool:
        """
        Проверка, является ли назначение выполняющим для всей формулы.
        """
        if np.any(assignment == -1):
            return False
        
        for i in range(len(self.clauses)):
            if not self.check_clause_satisfied(assignment, i):
                return False
        return True


# ============================================================================
# Модуль 3: Entropy Controller
# ============================================================================

class EntropyController:
    """
    Контроллер энтропии для динамической настройки параметров поиска.
    """
    
    def __init__(self, base_beam_size: int = 10, base_diversity: float = 0.1,
                 alpha: float = 2.0, beta: float = 1.5, window_size: int = 10):
        self.base_beam_size = base_beam_size
        self.base_diversity = base_diversity
        self.alpha = alpha
        self.beta = beta
        self.window_size = window_size
        
        self.prob_history = deque(maxlen=window_size)
        self.volume_history = deque(maxlen=window_size)
        
    def update(self, paths: List[BeamPath]) -> Tuple[int, float]:
        if not paths:
            return self.base_beam_size, self.base_diversity
        
        weights = np.array([p.weight for p in paths])
        
        # Вероятности на основе весов (меньший вес = выше вероятность)
        inv_weights = 1.0 / (weights + 1e-10)
        probs = inv_weights / np.sum(inv_weights)
        
        sum_squares = np.sum(probs ** 2)
        self.prob_history.append(sum_squares)
        
        if len(self.prob_history) > 1:
            volume = np.trapezoid(self.prob_history, dx=1.0)
        else:
            volume = sum_squares
        
        self.volume_history.append(volume)
        max_volume = max(self.volume_history) if self.volume_history else 1.0
        
        norm_volume = volume / max_volume if max_volume > 0 else 0.0
        
        new_beam_size = int(self.base_beam_size * (1 + self.alpha * norm_volume))
        new_diversity = self.base_diversity * (1 + self.beta * norm_volume)
        
        return max(1, new_beam_size), new_diversity


# ============================================================================
# Модуль 4: XOR-Teleporter
# ============================================================================

class XORTeleporter:
    """
    Телепортация для восстановления разнообразия лучей.
    """
    
    def __init__(self, viterbi_core: ViterbiCore, teleport_threshold: float = 0.3):
        self.viterbi = viterbi_core
        self.threshold = teleport_threshold
        self.teleport_count = 0
        
    def should_teleport(self, paths: List[BeamPath]) -> bool:
        """Проверка необходимости телепортации"""
        if len(paths) < 2:
            return False
        
        weights = [p.weight for p in paths]
        weight_std = np.std(weights)
        weight_mean = np.mean(weights)
        
        if weight_mean > 0:
            diversity_ratio = weight_std / weight_mean
        else:
            diversity_ratio = 1.0
        
        # Телепортируем, если разнообразие мало
        return diversity_ratio < self.threshold
    
    def teleport(self, paths: List[BeamPath], num_samples: int = 5) -> List[BeamPath]:
        """Генерация новых путей через XOR"""
        if len(paths) < 2:
            return paths
        
        new_paths = []
        
        # Пробуем несколько пар путей
        for _ in range(min(3, len(paths))):
            a, b = random.sample(paths, 2)
            
            # Направление = XOR определенных переменных
            direction = np.zeros(self.viterbi.num_vars, dtype=np.int8)
            defined_mask = (a.assignment != -1) & (b.assignment != -1)
            direction[defined_mask] = a.assignment[defined_mask] ^ b.assignment[defined_mask]
            
            # Пробуем разные точки на линии
            for t in np.linspace(0.2, 0.8, num_samples):
                new_assignment = a.assignment.copy()
                
                for i in range(self.viterbi.num_vars):
                    if direction[i] == 1 and new_assignment[i] != -1:
                        if random.random() < t:
                            new_assignment[i] ^= 1
                
                # Не добавляем дубликаты
                new_path = BeamPath(new_assignment, 0.0)
                if new_path.hash_id in self.viterbi.state_cache:
                    continue
                
                residual = self.viterbi.compute_residual(new_assignment)
                new_path.weight = residual
                new_paths.append(new_path)
                self.viterbi.state_cache.add(new_path.hash_id)
        
        self.teleport_count += 1
        return new_paths


# ============================================================================
# Модуль 5: Детектор UNSAT
# ============================================================================

class UNSATDetector:
    """
    Детектор невыполнимости.
    """
    
    def __init__(self, unsat_threshold: float = 0.5, patience: int = 3):
        self.unsat_threshold = unsat_threshold
        self.patience = patience
        self.consecutive_high_weight = 0
        self.best_weight = float('inf')
        
    def check(self, paths: List[BeamPath], teleporter: XORTeleporter) -> Tuple[bool, bool]:
        """
        Returns:
            (is_unsat, should_teleport)
        """
        if not paths:
            return True, False
        
        min_weight = min(p.weight for p in paths)
        
        # Обновляем лучший вес
        if min_weight < self.best_weight:
            self.best_weight = min_weight
            self.consecutive_high_weight = 0
        else:
            # Если вес не улучшается
            if min_weight >= self.best_weight:
                self.consecutive_high_weight += 1
        
        # UNSAT только если все пути имеют большой вес И нет улучшений
        all_high = all(p.weight > self.unsat_threshold for p in paths)
        
        if all_high and self.consecutive_high_weight >= self.patience:
            # Пробуем телепортацию перед объявлением UNSAT
            if teleporter.should_teleport(paths):
                return False, True
            else:
                return True, False
        
        # Телепортация при застое
        should_teleport = (self.consecutive_high_weight >= self.patience // 2 and 
                          teleporter.should_teleport(paths))
        
        return False, should_teleport


# ============================================================================
# Главный класс: EntropicBeamSATSolver
# ============================================================================

class EntropicBeamSATSolver:
    """
    Главный класс решателя SAT с энтропийным управлением лучом.
    """
    
    def __init__(self, cnf_formula: List[Set[int]], 
                 base_beam_size: int = 10,
                 base_diversity: float = 0.1,
                 alpha: float = 2.0,
                 beta: float = 1.5,
                 unsat_threshold: float = 0.5,
                 plot_live: bool = True):
        
        self.cnf = cnf_formula
        self.base_beam_size = base_beam_size
        self.base_diversity = base_diversity
        self.alpha = alpha
        self.beta = beta
        self.unsat_threshold = unsat_threshold
        self.plot_live = plot_live
        
        self.planner = PQPlanner(cnf_formula)
        self.controller = EntropyController(base_beam_size, base_diversity, alpha, beta)
        
        self.viterbi = None
        self.teleporter = None
        self.detector = None
        
        self.fig, self.ax = plt.subplots(figsize=(10, 6))
        self.energy_line = None
        self.energy_data = []
        self.iteration = 0
        
    def solve(self, timeout: float = 60.0) -> Tuple[bool, Optional[Dict[int, bool]], List[float]]:
        start_time = time.time()
        
        print("Вычисление порядка элиминации...")
        elimination_order = self.planner.compute_elimination_order()
        print(f"Порядок элиминации: {elimination_order}")
        
        self.viterbi = ViterbiCore(
            self.cnf, 
            elimination_order,
            self.base_beam_size,
            self.base_diversity
        )
        self.teleporter = XORTeleporter(self.viterbi, teleport_threshold=0.3)
        self.detector = UNSATDetector(self.unsat_threshold, patience=3)
        
        if self.plot_live:
            self._setup_plot()
        
        self.viterbi.initialize_paths()
        
        for i, var in enumerate(elimination_order):
            if time.time() - start_time > timeout:
                print(f"Таймаут после {i} переменных")
                break
            
            var_idx = self.viterbi.var_to_idx[var]
            
            # Динамическая настройка
            new_beam_size, new_diversity = self.controller.update(self.viterbi.paths)
            self.viterbi.beam_size = new_beam_size
            self.viterbi.diversity_lambda = new_diversity
            
            # Шаг поиска
            self.viterbi.paths = self.viterbi.beam_search_step(var_idx)
            
            # Проверка на SAT (полное назначение)
            for path in self.viterbi.paths:
                if np.all(path.assignment != -1):
                    if self.viterbi.is_satisfying_assignment(path.assignment):
                        assignment = {}
                        for idx, value in enumerate(path.assignment):
                            var = self.viterbi.idx_to_var[idx]
                            assignment[var] = bool(value)
                        print(f"Найдено выполняющее назначение на шаге {i}!")
                        return True, assignment, self.energy_data
            
            # Проверка на UNSAT
            is_unsat, should_teleport = self.detector.check(
                self.viterbi.paths, self.teleporter
            )
            
            if should_teleport:
                print(f"Телепортация на шаге {i} (веса: {[p.weight for p in self.viterbi.paths[:3]]})...")
                new_paths = self.teleporter.teleport(self.viterbi.paths)
                if new_paths:
                    all_paths = self.viterbi.paths + new_paths
                    all_paths.sort(key=lambda p: p.weight)
                    self.viterbi.paths = all_paths[:self.viterbi.beam_size]
            
            if is_unsat:
                print(f"Обнаружена невыполнимость на шаге {i}")
                return False, None, self.energy_data
            
            # Обновление статистики
            if self.viterbi.paths:
                min_weight = min(p.weight for p in self.viterbi.paths)
                self.energy_data.append(min_weight)
                
                if self.plot_live and i % 5 == 0:
                    self._update_plot(i)
        
        # Поиск лучшего пути
        if self.viterbi.paths:
            best_path = min(self.viterbi.paths, key=lambda p: p.weight)
            
            if np.all(best_path.assignment != -1):
                if self.viterbi.is_satisfying_assignment(best_path.assignment):
                    assignment = {}
                    for idx, value in enumerate(best_path.assignment):
                        var = self.viterbi.idx_to_var[idx]
                        assignment[var] = bool(value)
                    return True, assignment, self.energy_data
                else:
                    # Пытаемся доопределить переменные
                    print("Попытка доопределения переменных...")
                    return False, None, self.energy_data
            else:
                print("Не все переменные определены")
                return False, None, self.energy_data
        else:
            print("Не найдено путей")
            return False, None, self.energy_data
    
    def _setup_plot(self):
        self.ax.set_xlabel('Шаг')
        self.ax.set_ylabel('Энергия конфликта')
        self.ax.set_title('PQSAT v2.0: Динамика энергии конфликта')
        self.ax.grid(True, alpha=0.3)
        self.energy_line, = self.ax.plot([], [], 'b-', linewidth=2, label='Энергия')
        self.ax.legend()
        plt.ion()
        plt.show()
    
    def _update_plot(self, step: int):
        if not self.energy_data:
            return
        
        x = list(range(len(self.energy_data)))
        y = self.energy_data
        
        self.energy_line.set_data(x, y)
        self.ax.relim()
        self.ax.autoscale_view()
        
        if len(self.ax.lines) > 1:
            self.ax.lines[1].remove()
        self.ax.axhline(y=self.unsat_threshold, color='r', linestyle='--', 
                       alpha=0.5, label='UNSAT порог')
        
        plt.pause(0.01)


# ============================================================================
# Тестирование
# ============================================================================

def generate_test_formula(num_vars: int, num_clauses: int, sat: bool = True) -> List[Set[int]]:
    """Генерация тестовой формулы"""
    formula = []
    
    if sat:
        # Простая выполняемая формула: (x1) ∧ (x2) ∧ (x3) ∧ (x4) ∧ (x5)
        for i in range(1, num_vars + 1):
            formula.append({i})
    else:
        # Простая невыполнимая формула: (x1) ∧ (¬x1)
        formula.append({1})
        formula.append({-1})
        if num_vars > 1:
            formula.append({2})
            formula.append({-2})
    
    return formula


def main():
    print("=" * 60)
    print("PQSAT v2.0: Entropic Beam-SAT Solver")
    print("=" * 60)
    
    print(f"Версия NumPy: {np.__version__}")
    
    # Тест 1: Заведомо выполнимая формула
    print("\n--- Тест 1: Выполнимая формула (x1 ∧ x2 ∧ x3 ∧ x4 ∧ x5) ---")
    sat_formula = generate_test_formula(5, 5, sat=True)
    print(f"Формула: {sat_formula}")
    
    solver = EntropicBeamSATSolver(
        sat_formula,
        base_beam_size=10,
        base_diversity=0.1,
        unsat_threshold=0.5,
        plot_live=True
    )
    
    is_sat, assignment, energy = solver.solve(timeout=30)
    
    print(f"\nРезультат: {'SAT' if is_sat else 'UNSAT'}")
    if assignment:
        print(f"Назначение: {assignment}")
    print(f"Минимальная энергия: {min(energy) if energy else 'N/A'}")
    print(f"Телепортаций: {solver.teleporter.teleport_count if solver.teleporter else 0}")
    
    # Тест 2: Заведомо невыполнимая формула
    print("\n--- Тест 2: Невыполнимая формула (x1 ∧ ¬x1) ---")
    unsat_formula = generate_test_formula(1, 2, sat=False)
    print(f"Формула: {unsat_formula}")
    
    solver2 = EntropicBeamSATSolver(
        unsat_formula,
        base_beam_size=10,
        base_diversity=0.1,
        unsat_threshold=0.5,
        plot_live=False
    )
    
    is_sat, assignment, energy = solver2.solve(timeout=30)
    
    print(f"\nРезультат: {'SAT' if is_sat else 'UNSAT'}")
    print(f"Минимальная энергия: {energy[-1] if energy else 'N/A'}")
    
    # Сохраняем график
    if solver.energy_data:
        plt.figure(figsize=(10, 6))
        plt.plot(solver.energy_data, 'b-', linewidth=2, label='Энергия конфликта')
        plt.axhline(y=solver.unsat_threshold, color='r', linestyle='--', 
                   alpha=0.5, label='UNSAT порог')
        plt.xlabel('Шаг')
        plt.ylabel('Энергия конфликта')
        plt.title('PQSAT v2.0: Динамика энергии конфликта')
        plt.grid(True, alpha=0.3)
        plt.legend()
        plt.savefig('pqsat_energy.png', dpi=150)
        print("\nГрафик сохранен как 'pqsat_energy.png'")
        plt.show()


if __name__ == "__main__":
    main()
