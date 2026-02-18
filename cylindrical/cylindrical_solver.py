"""
3-SAT Solver "Cylindrical Gravity Prototyper"
Реализация на основе статической цилиндрической модели с гравитацией и туннелированием.
Добавлен механизм рефрактерности (cooldown) для переменных.
"""

import networkx as nx
import numpy as np
import random
import math
from collections import defaultdict
import time
import signal
from functools import wraps
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict, Any


class TimeoutError(Exception):
    """Исключение при таймауте."""
    pass


def timeout_handler(seconds):
    """Декоратор для таймаута функции."""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            def signal_handler(signum, frame):
                raise TimeoutError(f"Функция {func.__name__} превысила таймаут {seconds} сек")
            
            signal.signal(signal.SIGALRM, signal_handler)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result
        return wrapper
    return decorator


@dataclass
class VariableState:
    """Состояние переменной в цилиндре."""
    index: int
    tension: float = 0.0
    radius: float = 1.0
    pressure: float = 0.0
    energy_barrier: float = 0.0
    cooldown: int = 0
    last_flip_step: int = -1
    flip_count: int = 0
    
    def can_flip(self, current_step: int) -> bool:
        """Проверяет, можно ли перевернуть переменную."""
        return self.cooldown == 0
    
    def update_cooldown(self, current_step: int, cooldown_value: int):
        """Устанавливает период охлаждения."""
        self.cooldown = cooldown_value
        self.last_flip_step = current_step
        self.flip_count += 1
    
    def tick_cooldown(self):
        """Уменьшает cooldown на 1."""
        if self.cooldown > 0:
            self.cooldown -= 1


class CylinderSolver:
    """
    3-SAT солвер на основе цилиндрической модели с гравитацией.
    
    Топология:
    - Переменные на экваторе цилиндра
    - Хорновские клаузы на левом полюсе
    - Двойные хорновские клаузы на правом полюсе
    - Положительные литералы → левый полюс, отрицательные → правый
    
    Механизмы:
    - Напряжение T(v) - разница нарушений при перевороте
    - Радиус R(v) - гравитация (уменьшается с напряжением)
    - Давление P(v) - T(v) + влияние соседей
    - Рефрактерность - cooldown после флипа
    - Энергетический пробой - каскадное влияние при флипе
    """
    
    def __init__(self, n_vars, clauses, seed=None, verbose=False, 
                 cooldown_base=5, cooldown_variance=2):
        """
        Инициализация солвера.
        
        Args:
            n_vars: количество переменных
            clauses: список дизъюнктов
            seed: seed для воспроизводимости
            verbose: выводить отладочную информацию
            cooldown_base: базовая длительность охлаждения
            cooldown_variance: вариативность охлаждения
        """
        if seed is not None:
            random.seed(seed)
            np.random.seed(seed)
        
        self.n_vars = n_vars
        self.clauses = clauses
        self.n_clauses = len(clauses)
        self.verbose = verbose
        self.cooldown_base = cooldown_base
        self.cooldown_variance = cooldown_variance
        
        # Текущее присваивание
        self.assignment = [random.choice([True, False]) for _ in range(n_vars)]
        
        # Состояния переменных
        self.vars = [VariableState(i) for i in range(n_vars)]
        
        # Кэш для быстрого подсчета
        self.var_to_clauses = defaultdict(list)
        self.clause_to_vars = []  # Для каждой клаузы - список переменных
        self._build_indices()
        
        # Граф для гравитационного дрейфа
        self.graph = nx.Graph()
        self._build_graph()
        
        # Вормхолы
        self.wormholes = []
        
        # Статистика
        self.step = 0
        self.best_energy = self.n_clauses
        self.best_assignment = self.assignment.copy()
        self.energy_history = []
        self.cooldown_history = []  # История среднего cooldown
        
        # Обновляем метрики
        self._update_all_metrics()
    
    def _build_indices(self):
        """Строит индексы для быстрого доступа."""
        for idx, clause in enumerate(self.clauses):
            vars_in_clause = [abs(lit) - 1 for lit in clause]
            self.clause_to_vars.append(vars_in_clause)
            for v in set(vars_in_clause):
                self.var_to_clauses[v].append(idx)
    
    def _build_graph(self):
        """Строит граф связей между переменными."""
        for v in range(self.n_vars):
            self.graph.add_node(v)
        
        for clause in self.clauses:
            vars_in_clause = list(set(abs(lit) - 1 for lit in clause))
            for i in range(len(vars_in_clause)):
                for j in range(i+1, len(vars_in_clause)):
                    v1, v2 = vars_in_clause[i], vars_in_clause[j]
                    if v1 != v2:
                        if self.graph.has_edge(v1, v2):
                            self.graph[v1][v2]['weight'] += 1
                        else:
                            self.graph.add_edge(v1, v2, weight=1)
    
    def _count_violations(self, assignment=None):
        """Подсчитывает количество нарушенных клауз."""
        if assignment is None:
            assignment = self.assignment
        
        violations = 0
        for clause in self.clauses:
            satisfied = False
            for lit in clause:
                var_idx = abs(lit) - 1
                is_true = assignment[var_idx]
                if (lit > 0 and is_true) or (lit < 0 and not is_true):
                    satisfied = True
                    break
            if not satisfied:
                violations += 1
        return violations
    
    def _update_tension(self):
        """Обновляет напряжение T(v) для всех переменных."""
        # Сбрасываем напряжение
        for v in self.vars:
            v.tension = 0.0
        
        # Для каждой переменной
        for v_idx, v in enumerate(self.vars):
            current_true = self.assignment[v_idx]
            
            # Проверяем все клаузы с этой переменной
            for clause_idx in self.var_to_clauses[v_idx]:
                clause = self.clauses[clause_idx]
                
                # Текущее состояние клаузы
                satisfied_current = False
                for lit in clause:
                    var_idx = abs(lit) - 1
                    if (lit > 0 and self.assignment[var_idx]) or (lit < 0 and not self.assignment[var_idx]):
                        satisfied_current = True
                        break
                
                # Состояние после переворота v
                temp_assignment = self.assignment.copy()
                temp_assignment[v_idx] = not current_true
                
                satisfied_flipped = False
                for lit in clause:
                    var_idx = abs(lit) - 1
                    if (lit > 0 and temp_assignment[var_idx]) or (lit < 0 and not temp_assignment[var_idx]):
                        satisfied_flipped = True
                        break
                
                # Обновляем напряжение
                if not satisfied_current and satisfied_flipped:
                    v.tension += 1.0
                elif satisfied_current and not satisfied_flipped:
                    v.tension -= 1.0
    
    def _update_radius(self):
        """Обновляет радиус R(v) на основе напряжения."""
        max_tension = max(1.0, max(abs(v.tension) for v in self.vars))
        
        for v in self.vars:
            # Нормализованное напряжение
            norm_tension = v.tension / max_tension
            
            # Радиус по сигмоиде
            k = 2.0
            v.radius = 1.0 / (1.0 + math.exp(k * norm_tension))
            v.radius = max(0.1, min(1.0, v.radius))
            
            # Обновляем граф
            self.graph.nodes[v.index]['radius'] = v.radius
            self.graph.nodes[v.index]['tension'] = v.tension
    
    def _update_pressure(self):
        """Обновляет давление P(v)."""
        for v in self.vars:
            # Гравитационное влияние соседей
            neighbor_influence = 0
            total_weight = 0
            
            for neighbor_idx in self.graph.neighbors(v.index):
                neighbor = self.vars[neighbor_idx]
                weight = self.graph[v.index][neighbor_idx].get('weight', 1)
                gravity = 1.0 - neighbor.radius
                neighbor_influence += gravity * weight * neighbor.tension
                total_weight += weight
            
            if total_weight > 0:
                neighbor_influence /= total_weight
            
            # Давление = напряжение + влияние соседей
            v.pressure = v.tension + 0.3 * neighbor_influence
            self.graph.nodes[v.index]['pressure'] = v.pressure
    
    def _update_energy_barrier(self):
        """Обновляет энергетический барьер."""
        for v in self.vars:
            if v.tension >= 0:
                v.energy_barrier = 0
            else:
                v.energy_barrier = -v.tension
    
    def _update_wormholes(self):
        """Создает вормхолы между переменными с высоким напряжением."""
        self.wormholes.clear()
        
        if self.n_vars < 5:
            return
        
        # Топ-20% по напряжению
        tensions = [v.tension for v in self.vars]
        if not tensions:
            return
            
        threshold = np.percentile(tensions, 80) if len(tensions) > 1 else max(tensions)
        
        high_tension_vars = [v.index for v in self.vars if v.tension > threshold]
        
        if len(high_tension_vars) < 2:
            return
        
        # Создаем вормхолы
        max_wormholes = min(10, len(high_tension_vars) * (len(high_tension_vars) - 1) // 2)
        
        for _ in range(max_wormholes):
            if len(high_tension_vars) < 2:
                break
            
            v1, v2 = random.sample(high_tension_vars, 2)
            
            if nx.has_path(self.graph, v1, v2):
                try:
                    dist = nx.shortest_path_length(self.graph, v1, v2)
                    if dist > 2:
                        tension_sum = abs(self.vars[v1].tension) + abs(self.vars[v2].tension)
                        prob = tension_sum / (2 * max(1, threshold))
                        if random.random() < min(1.0, prob):
                            self.wormholes.append((v1, v2))
                except nx.NetworkXNoPath:
                    pass
    
    def _tick_cooldowns(self):
        """Уменьшает cooldown всех переменных на 1."""
        for v in self.vars:
            v.tick_cooldown()
    
    def _get_available_vars(self):
        """Возвращает список переменных, доступных для флипа."""
        return [v for v in self.vars if v.can_flip(self.step)]
    
    def _get_cooldown_stats(self):
        """Возвращает статистику по cooldown."""
        active = sum(1 for v in self.vars if v.cooldown > 0)
        avg_cooldown = np.mean([v.cooldown for v in self.vars]) if self.vars else 0
        max_cooldown = max((v.cooldown for v in self.vars), default=0)
        return active, avg_cooldown, max_cooldown
    
    def _find_oldest_cooldown(self):
        """
        Находит переменную с самым старым cooldown.
        Возвращает индекс переменной или None, если все доступны.
        """
        if not self.vars:
            return None
        
        # Ищем переменные в cooldown
        in_cooldown = [v for v in self.vars if v.cooldown > 0]
        if not in_cooldown:
            return None
        
        # Самая старая (минимальный last_flip_step)
        oldest = min(in_cooldown, key=lambda v: v.last_flip_step)
        return oldest.index
    
    def _cool_down_system(self, factor=0.5):
        """
        'Остужает' систему - уменьшает cooldown всех переменных.
        
        Args:
            factor: коэффициент уменьшения (0.5 = уменьшить вдвое)
        """
        if self.verbose:
            active_before, avg_before, _ = self._get_cooldown_stats()
            print(f"   🌡️ Системное охлаждение: {active_before} переменных в бане, "
                  f"средний cooldown {avg_before:.1f}")
        
        for v in self.vars:
            if v.cooldown > 0:
                v.cooldown = max(0, int(v.cooldown * factor))
        
        if self.verbose:
            active_after, avg_after, _ = self._get_cooldown_stats()
            print(f"   ❄️ После охлаждения: {active_after} переменных, "
                  f"средний cooldown {avg_after:.1f}")
    
    def _energy_breakthrough(self, flipped_var_idx):
        """
        Энергетический пробой - при флипе переменной с высоким напряжением
        увеличиваем давление на связанные переменные.
        
        Args:
            flipped_var_idx: индекс перевернутой переменной
        """
        flipped_var = self.vars[flipped_var_idx]
        
        # Проверяем, был ли флип действительно энергетическим
        if abs(flipped_var.tension) < 1.0:
            return
        
        # Находим все переменные, связанные через общие клаузы
        affected_vars = set()
        
        for clause_idx in self.var_to_clauses[flipped_var_idx]:
            for v_idx in self.clause_to_vars[clause_idx]:
                if v_idx != flipped_var_idx:
                    affected_vars.add(v_idx)
        
        if not affected_vars:
            return
        
        if self.verbose:
            print(f"   ⚡ Энергетический пробой! Влияет на {len(affected_vars)} переменных")
        
        # Увеличиваем давление на связанные переменные
        breakthrough_power = abs(flipped_var.tension) / max(1, len(affected_vars))
        
        for v_idx in affected_vars:
            v = self.vars[v_idx]
            # Увеличиваем давление пропорционально напряжению флипнутой переменной
            pressure_boost = breakthrough_power * (1.0 - v.radius)
            v.pressure += pressure_boost
            
            # Также немного уменьшаем cooldown (эффект "разогрева")
            if v.cooldown > 0:
                v.cooldown = max(0, v.cooldown - 1)
    
    def _update_all_metrics(self):
        """Обновляет все метрики."""
        self._update_tension()
        self._update_radius()
        self._update_pressure()
        self._update_energy_barrier()
        self._update_wormholes()
        
        # Сохраняем историю
        current_energy = self._count_violations()
        self.energy_history.append(current_energy)
        
        active, avg_cooldown, _ = self._get_cooldown_stats()
        self.cooldown_history.append(avg_cooldown)
        
        # Обновляем лучшее решение
        if current_energy < self.best_energy:
            self.best_energy = current_energy
            self.best_assignment = self.assignment.copy()
    
    def gravity_drift(self):
        """Гравитационный дрейф."""
        for v in self.vars:
            if v.radius < 0.4:  # Высокая гравитация
                for neighbor_idx in self.graph.neighbors(v.index):
                    current_weight = self.graph[v.index][neighbor_idx].get('weight', 1)
                    gravity_boost = 1.0 + (0.4 - v.radius) * 2
                    new_weight = current_weight * gravity_boost
                    self.graph[v.index][neighbor_idx]['weight'] = min(10.0, new_weight)
    
    def find_cluster_for_wormhole(self, wormhole):
        """Находит кластер для вормхола."""
        v1, v2 = wormhole
        cluster = {v1, v2}
        
        common_neighbors = set(self.graph.neighbors(v1)) & set(self.graph.neighbors(v2))
        for neighbor in common_neighbors:
            if self.vars[neighbor].tension > 0:
                cluster.add(neighbor)
        
        return list(cluster)
    
    def try_cluster_flip(self, cluster):
        """Пытается перевернуть кластер."""
        if len(cluster) < 2:
            return False
        
        # Проверяем, все ли переменные в кластере доступны
        for v_idx in cluster:
            if not self.vars[v_idx].can_flip(self.step):
                return False
        
        old_assignment = self.assignment.copy()
        old_energy = self._count_violations()
        
        for v_idx in cluster:
            self.assignment[v_idx] = not self.assignment[v_idx]
        
        new_energy = self._count_violations()
        
        if new_energy < old_energy:
            # Успешный кластерный флип
            for v_idx in cluster:
                cooldown = self.cooldown_base + random.randint(-self.cooldown_variance, 
                                                              self.cooldown_variance)
                self.vars[v_idx].update_cooldown(self.step, max(1, cooldown))
            
            if self.verbose:
                print(f"   🕳️ Кластерный переворот! {cluster} "
                      f"энергия: {old_energy} -> {new_energy}")
            return True
        else:
            self.assignment = old_assignment
            return False
    
    def select_variable_to_flip(self):
        """
        Выбирает переменную для флипа с учетом рефрактерности.
        
        Returns:
            (var_index, forced) - индекс переменной и был ли флип принудительным
        """
        available_vars = self._get_available_vars()
        
        if not available_vars:
            # Все переменные в бане - кризис!
            if self.verbose:
                print("   ⚠️ Все переменные в бане! Ищем выход...")
            
            # Пробуем найти самую старую
            oldest_idx = self._find_oldest_cooldown()
            if oldest_idx is not None:
                if self.verbose:
                    v = self.vars[oldest_idx]
                    print(f"   🔄 Принудительный флип самой старой var {oldest_idx+1} "
                          f"(cooldown={v.cooldown})")
                return oldest_idx, True
            
            # Если ничего не помогает - охлаждаем систему
            self._cool_down_system(factor=0.3)
            available_vars = self._get_available_vars()
            
            if available_vars:
                # Выбираем по давлению
                best_var = max(available_vars, key=lambda v: v.pressure)
                return best_var.index, True
        
        # Нормальный режим - выбираем по давлению
        if available_vars:
            # Сортируем по давлению
            available_vars.sort(key=lambda v: v.pressure, reverse=True)
            
            # Выбираем с вероятностью, пропорциональной давлению
            pressures = [max(0, v.pressure) for v in available_vars[:5]]  # Топ-5
            total_pressure = sum(pressures)
            
            if total_pressure > 0 and len(available_vars) > 1:
                # Вероятностный выбор
                probs = [p / total_pressure for p in pressures]
                chosen_idx = np.random.choice(len(available_vars[:5]), p=probs)
                return available_vars[chosen_idx].index, False
            else:
                # Если давления нет или мало вариантов - просто лучший
                return available_vars[0].index, False
        
        # Запасной вариант
        return random.randint(0, self.n_vars - 1), True
    
    def active_tunneling_step(self):
        """
        Выполняет один шаг активного туннелирования с учетом рефрактерности.
        """
        self.step += 1
        
        # Уменьшаем cooldown у всех
        self._tick_cooldowns()
        
        # Текущая энергия
        current_energy = self._count_violations()
        
        # Выбираем переменную для флипа
        var_idx, forced = self.select_variable_to_flip()
        
        # Запоминаем состояние до флипа
        old_value = self.assignment[var_idx]
        old_tension = self.vars[var_idx].tension
        
        # Переворачиваем
        self.assignment[var_idx] = not old_value
        
        # Устанавливаем cooldown для перевернутой переменной
        if not forced:
            # Нормальный флип - стандартный cooldown
            cooldown = self.cooldown_base + random.randint(-self.cooldown_variance, 
                                                          self.cooldown_variance)
        else:
            # Принудительный флип - меньший cooldown
            cooldown = max(1, self.cooldown_base // 2)
        
        self.vars[var_idx].update_cooldown(self.step, cooldown)
        
        # Энергетический пробой, если напряжение было высоким
        if abs(old_tension) > 1.0:
            self._energy_breakthrough(var_idx)
        
        # Гравитационный дрейф
        self.gravity_drift()
        
        # Пробуем кластерные перевороты
        cluster_flipped = False
        if self.wormholes and random.random() < 0.2:
            wormhole = random.choice(self.wormholes)
            cluster = self.find_cluster_for_wormhole(wormhole)
            if self.try_cluster_flip(cluster):
                cluster_flipped = True
        
        # Обновляем метрики
        self._update_all_metrics()
        
        # Статистика по cooldown
        active_cooldown, avg_cooldown, max_cooldown = self._get_cooldown_stats()
        
        return {
            'step': self.step,
            'energy': self._count_violations(),
            'min_radius': min(v.radius for v in self.vars),
            'flipped_var': var_idx + 1,  # 1-индексация для вывода
            'forced': forced,
            'pressure': self.vars[var_idx].pressure,
            'wormholes': len(self.wormholes),
            'active_cooldown': active_cooldown,
            'avg_cooldown': avg_cooldown,
            'cluster_flipped': cluster_flipped
        }
    
    def solve(self, max_steps=10000, timeout=60, target_energy=0, verbose=True):
        """
        Запускает солвер.
        
        Returns:
            (sat, assignment, stats)
        """
        start_time = time.time()
        
        if verbose:
            print(f"\n{'='*70}")
            print(f"🚀 Запуск солвера: {self.n_vars} переменных, {self.n_clauses} клауз")
            print(f"   Рефрактерность: base={self.cooldown_base}, var={self.cooldown_variance}")
            print(f"{'='*70}")
            print(f"{'Шаг':>6} | {'Энергия':>8} | {'Мин R':>8} | {'Var':>6} | "
                  f"{'Cooldown':>8} | {'Вормхолы':>8} | {'Время':>8}")
            print("-"*80)
        
        # Основной цикл
        for step in range(max_steps):
            elapsed = time.time() - start_time
            if elapsed > timeout:
                if verbose:
                    print(f"\n⏱️ Таймаут ({timeout} сек)")
                break
            
            info = self.active_tunneling_step()
            
            # Логирование
            if verbose and (step % 10 == 0 or info['energy'] == 0 or info['forced']):
                forced_marker = "⚡" if info['forced'] else " "
                cluster_marker = "🕳️" if info.get('cluster_flipped', False) else " "
                print(f"{info['step']:6d} | {info['energy']:8d} | {info['min_radius']:8.3f} | "
                      f"{forced_marker}{info['flipped_var']:>4} | "
                      f"{info['active_cooldown']:3d}/{info['avg_cooldown']:3.1f} | "
                      f"{info['wormholes']:8d} | {elapsed:8.2f}s{cluster_marker}")
            
            if info['energy'] == target_energy:
                if verbose:
                    print(f"\n✅ SAT решение найдено за {step+1} шагов!")
                return True, self.assignment, {
                    'steps': step+1,
                    'time': elapsed,
                    'final_energy': 0,
                    'best_energy': 0,
                    'cooldown_stats': self._get_cooldown_stats()
                }
        
        elapsed = time.time() - start_time
        
        if verbose:
            print(f"\n⚠️ Решение не найдено. Лучшая энергия: {self.best_energy}")
        
        return False, self.best_assignment, {
            'steps': max_steps,
            'time': elapsed,
            'final_energy': self._count_violations(),
            'best_energy': self.best_energy,
            'cooldown_stats': self._get_cooldown_stats()
        }
    
    def print_state(self):
        """Выводит текущее состояние."""
        print("\n" + "="*70)
        print("📊 Текущее состояние цилиндра")
        print("="*70)
        print(f"Шаг: {self.step}")
        print(f"Нарушенных клауз: {self._count_violations()}/{self.n_clauses}")
        print(f"Мин радиус: {min(v.radius for v in self.vars):.3f}")
        print(f"Макс напряжение: {max(v.tension for v in self.vars):.3f}")
        print(f"Вормхолов: {len(self.wormholes)}")
        
        active, avg_cd, max_cd = self._get_cooldown_stats()
        print(f"\n🌡️ Рефрактерность:")
        print(f"   В бане: {active}/{self.n_vars} переменных")
        print(f"   Средний cooldown: {avg_cd:.1f}")
        print(f"   Макс cooldown: {max_cd}")
        
        # Топ переменных
        if self.n_vars > 0:
            print("\n🔥 Топ переменных по давлению:")
            top_n = min(5, self.n_vars)
            sorted_vars = sorted(self.vars, key=lambda v: v.pressure, reverse=True)[:top_n]
            for v in sorted_vars:
                cd_status = f"(🔥 баня {v.cooldown})" if v.cooldown > 0 else ""
                print(f"  var {v.index+1}: P={v.pressure:.2f}, "
                      f"T={v.tension:.2f}, R={v.radius:.3f} {cd_status}")
