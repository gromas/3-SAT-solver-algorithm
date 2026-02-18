import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.patches import Circle
from collections import defaultdict, deque
import random
import math
import os
import glob
from pathlib import Path

# ==================== DIMACS LOADER ====================
def parse_dimacs_cnf(filepath):
    """
    Парсит DIMACS CNF файл.
    Возвращает: (n, clauses)
    """
    clauses = []
    n = 0
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('%') or line.startswith('0'):
                continue
            if line.startswith('p'):
                parts = line.split()
                if len(parts) >= 3:
                    n = int(parts[2])
                continue
            try:
                nums = list(map(int, line.split()))
            except ValueError:
                continue
            if nums and nums[-1] == 0:
                nums = nums[:-1]
            if nums:
                clauses.append(nums)
    return n, clauses

def load_benchmark_folder(folder_path):
    """
    Загружает все .cnf файлы из папки.
    Возвращает список кортежей (имя_файла, n, clauses)
    """
    benchmarks = []
    cnf_files = glob.glob(os.path.join(folder_path, "*.cnf"))
    
    for cnf_file in cnf_files:
        try:
            n, clauses = parse_dimacs_cnf(cnf_file)
            benchmarks.append((os.path.basename(cnf_file), n, clauses))
        except Exception as e:
            print(f"Ошибка загрузки {cnf_file}: {e}")
    
    return benchmarks

def get_random_benchmark(folder_path):
    """
    Берёт случайный .cnf файл из папки.
    """
    benchmarks = load_benchmark_folder(folder_path)
    if not benchmarks:
        return None
    return random.choice(benchmarks)

def print_benchmark_info(benchmark):
    """
    Красиво выводит информацию о бенчмарке.
    """
    name, n, clauses = benchmark
    print(f"\n{'='*60}")
    print(f"📊 Бенчмарк: {name}")
    print(f"{'='*60}")
    print(f"Переменных: {n}")
    print(f"Дизъюнктов: {len(clauses)}")
    print(f"Плотность: {len(clauses)/n:.2f}")
    
    # Статистика по длинам дизъюнктов
    lengths = [len(c) for c in clauses]
    print(f"\nДлины дизъюнктов:")
    print(f"  min: {min(lengths)}")
    print(f"  max: {max(lengths)}")
    print(f"  среднее: {sum(lengths)/len(lengths):.2f}")
    
    # Первые 5 дизъюнктов для примера
    print(f"\nПервые 5 дизъюнктов:")
    for i, clause in enumerate(clauses[:5]):
        print(f"  {i+1}: {clause}")
    
    return name, n, clauses


# ==================== DONUT SAT VISUALIZER WITH GEAR EFFECT ====================
class DonutSATVisualizer:
    def __init__(self, n_vars, clauses, benchmark_name="Unknown"):
        self.clauses = clauses
        self.n_vars = n_vars
        self.benchmark_name = benchmark_name
        self.variables = set(range(1, n_vars + 1))
        self.horn_clauses = set()
        self.dual_horn_clauses = set()
        self.xor_clauses = set()
        self.var_to_clauses = defaultdict(list)
        
        # Параметры эффекта шестеренок
        self.K = 0.3  # Коэффициент жесткости
        self.gear_inertia = {}  # Инерция для каждой переменной (зависит от числа узлов)
        
        # Построение индексов
        for idx, clause in enumerate(self.clauses):
            for lit in clause:
                var = abs(lit)
                if 1 <= var <= n_vars:
                    self.var_to_clauses[var].append(idx)
        
        self.classify_clauses()
        
        # Параметры симуляции
        self.var_values = np.random.uniform(-1, 1, self.n_vars + 1)
        self.var_phases = np.random.uniform(0, 2*np.pi, self.n_vars + 1)
        self.var_phases_velocity = np.zeros(self.n_vars + 1)  # Скорость вращения
        self.time = 0
        self.history = []
        self.rms_history = []
        
        # Для эффекта дребезга
        self.jitter_amplitude = np.zeros(self.n_vars + 1)  # Амплитуда вибрации
        self.jitter_phase = np.random.uniform(0, 2*np.pi, self.n_vars + 1)  # Фаза вибрации
        self.jitter_history = defaultdict(lambda: deque(maxlen=100))  # История дребезга для каждой переменной
        self.jitter_radius = np.ones(self.n_vars + 1)  # Радиус для визуализации дребезга
        self.flash_intensity = np.zeros(self.n_vars + 1)  # Интенсивность вспышки
        
        # Для детектора UNSAT
        self.amplitude_history = deque(maxlen=150)  # История амплитуды (5 оборотов * 30 шагов)
        self.unsat_detected = False
        self.cycle_frequency = 0
        self.rotation_count = 0
        self.last_rotation_phase = 0
        
        # Создание структуры узлов для каждой переменной
        self.build_variable_nodes()
        
        # Вычисление инерции (чем больше узлов, тем тяжелее шестеренка)
        for var in range(1, self.n_vars + 1):
            n_nodes = len(self.var_nodes.get(var, []))
            self.gear_inertia[var] = 1.0 / (1.0 + 0.1 * n_nodes)  # Больше узлов = больше инерция
        
        # Параметры визуализации
        self.fig = plt.figure(figsize=(18, 10))
        self.left_ax = self.fig.add_subplot(121)
        self.right_ax = self.fig.add_subplot(122)
        self.donut_positions = {}
        self.donut_radius = 0.8
        self.setup_visualization()
        
        # Статистика
        self.solution_found = False
        self.solution_time = 0
    
    def classify_clauses(self):
        """Классификация клауз на Horn, Dual-Horn и XOR"""
        for idx, clause in enumerate(self.clauses):
            pos_lits = sum(1 for lit in clause if lit > 0)
            neg_lits = len(clause) - pos_lits
            
            # Horn: максимум одна положительная литера
            if pos_lits <= 1:
                self.horn_clauses.add(idx)
            
            # Dual-Horn: максимум одна отрицательная литера
            if neg_lits <= 1:
                self.dual_horn_clauses.add(idx)
            
            # Поиск XOR структуры (a ⊕ b = c)
            if len(clause) == 3:
                # Проверка на наличие двух отрицаний
                neg_count = sum(1 for lit in clause if lit < 0)
                if neg_count in [1, 2]:
                    self.xor_clauses.add(idx)
    
    def build_variable_nodes(self):
        """Построение полярных узлов: Сектор H (Horn) и Сектор DH (Dual-Horn)"""
        self.var_nodes = {}
        
        # 1. Сначала классифицируем ВСЕ клаузы (если еще не сделано)
        h_clauses_indices = []
        dh_clauses_indices = []
        
        for idx, clause in enumerate(self.clauses):
            pos_count = sum(1 for lit in clause if lit > 0)
            if pos_count <= 1: # Ваше определение Horn
                h_clauses_indices.append(idx)
            else:              # Ваше определение Dual-Horn
                dh_clauses_indices.append(idx)

        # 2. Теперь строим бублики для каждой переменной
        for var in range(1, self.n_vars + 1):
            clauses_for_var = self.var_to_clauses.get(var, [])
            if clauses_for_var:
                # Фильтруем те, что относятся к H, и те, что к DH
                var_h = [c for c in clauses_for_var if c in h_clauses_indices]
                var_dh = [c for c in clauses_for_var if c in dh_clauses_indices]
                
                # Собираем: Сначала сектор "Отрицательного давления", затем "Положительного"
                ordered_clauses = var_h + var_dh
                
                angles = np.linspace(0, 2*np.pi, len(ordered_clauses), endpoint=False)
                self.var_nodes[var] = list(zip(ordered_clauses, angles))
                
                n_clauses = len(self.var_to_clauses.get(var, []))
                # Нелинейная инерция: чем больше клауз, тем МЕНЬШЕ скорость реакции
                # Для 3 клауз: инерция ~ 0.5 (быстрая)
                # Для 15 клауз: инерция ~ 0.02 (очень тяжелая)
                self.gear_inertia[var] = 1.0 / (1.0 + np.power(n_clauses, 1.5)) 
    
    def setup_visualization(self):
        """Настройка визуализации"""
        # Позиции для бубликов (сетка)
        grid_size = int(np.ceil(np.sqrt(self.n_vars)))
        for var in range(1, self.n_vars + 1):
            row = (var - 1) // grid_size
            col = (var - 1) % grid_size
            # Центрируем сетку
            x = col * 4 - (grid_size - 1) * 2
            y = -row * 4 + (grid_size - 1) * 2
            self.donut_positions[var] = (x, y)
    
    def get_clause_color(self, clause_idx):
        """Определение цвета узла по типу клаузы"""
        if clause_idx in self.horn_clauses:
            return 'red'
        elif clause_idx in self.dual_horn_clauses:
            return 'blue'
        elif clause_idx in self.xor_clauses:
            return 'green'
        else:
            return 'gray'
    
    def clause_satisfied(self, clause, values):
        """Проверка удовлетворения клаузы"""
        for lit in clause:
            var = abs(lit)
            if var > self.n_vars:
                continue
            var_val = values[var]
            if lit > 0 and var_val > 0:
                return True
            elif lit < 0 and var_val < 0:
                return True
        return False
    
    def get_clause_satisfaction_degree(self, clause, values):
        """Степень удовлетворения клаузы (непрерывная)"""
        max_sat = 0
        for lit in clause:
            var = abs(lit)
            if var > self.n_vars:
                continue
            var_val = values[var]
            if lit > 0:
                sat = max(0, var_val)
            else:
                sat = max(0, -var_val)
            max_sat = max(max_sat, sat)
        return max_sat
    
    def get_expected_phase_for_var(self, var, clause):
        """Определяет ожидаемую фазу для переменной в клаузе"""
        # Ожидаемая фаза зависит от знака литеры и текущего состояния
        for lit in clause:
            if abs(lit) == var:
                # Если литера положительная, ожидаем фазу ~0 (значение >0)
                # Если отрицательная, ожидаем фазу ~π (значение <0)
                return 0 if lit > 0 else np.pi
        return 0
    
    def update_dynamics_with_gear_effect(self):
        """Обновление динамики с эффектом шестеренок"""
        self.time += 0.05
        self.rotation_count += 0.05
        
        # Сброс ускорений
        phase_accelerations = np.zeros(self.n_vars + 1)
        self.jitter_amplitude.fill(0)
        
        # ЭФФЕКТ ШЕСТЕРЕНОК: Phase Kick от неудовлетворенных клауз
        for clause_idx, clause in enumerate(self.clauses):
            if not self.clause_satisfied(clause, self.var_values):
                # Клауза не удовлетворена - создает фазовые удары
                for lit in clause:
                    var = abs(lit)
                    if var > self.n_vars:
                        continue
                    
                    # Определяем ожидаемую фазу для этой переменной
                    expected_phase = self.get_expected_phase_for_var(var, clause)
                    current_phase = self.var_phases[var]
                    
                    # Фазовый удар с учетом инерции шестеренки
                    phase_error = np.sin(expected_phase - current_phase)
                    kick_strength = self.K * phase_error * self.gear_inertia[var]
                    
                    phase_accelerations[var] += kick_strength
                    
                    # ЭФФЕКТ ДРЕБЕЗГА: запоминаем амплитуду удара
                    self.jitter_amplitude[var] += abs(kick_strength) * 0.5
                    self.flash_intensity[var] = min(1.0, self.flash_intensity[var] + abs(kick_strength))
        
        # Обновление фаз с учетом ускорений
        for var in range(1, self.n_vars + 1):
        
            """
            # Принудительная блокировка шестеренки
            if var == 3:
                #self.var_phases_velocity[var] = 0.0  # Скорость ноль
                #self.var_phases[var] = 0.0           # Фаза стоит на месте
                #self.jitter_radius[var] = 1.0        # Радиус не дрожит
                #self.var_values[var] = 0.0           # Логическое значение нейтрально
                self.gear_inertia[var] = 0.01
                continue                             # Пропускаем остальные расчеты для этой переменной
            """
        
            # Базовое вращение
            base_speed = 0.1
            
            # Добавляем фазовый удар
            self.var_phases_velocity[var] = base_speed + phase_accelerations[var]
            
            # Обновляем фазу
            self.var_phases[var] += self.var_phases_velocity[var] * 0.1
            
            # Эффект дребезга (вибрация радиуса)
            self.jitter_amplitude[var] = min(0.3, self.jitter_amplitude[var])  # Ограничение
            self.jitter_phase[var] += 0.5  # Быстрая фаза для дребезга
            self.jitter_radius[var] = 1.0 + self.jitter_amplitude[var] * np.sin(self.jitter_phase[var])
            
            # Затухание вспышки
            self.flash_intensity[var] *= 0.95
            
            # Сохраняем историю дребезга
            self.jitter_history[var].append(self.jitter_amplitude[var])
        
        # Обновление значений переменных под давлением (как и раньше)
        pressures = np.zeros(self.n_vars + 1)
        for clause_idx, clause in enumerate(self.clauses):
            sat_degree = self.get_clause_satisfaction_degree(clause, self.var_values)
            if sat_degree < 0.8:
                for lit in clause:
                    var = abs(lit)
                    if var > self.n_vars:
                        continue
                    target = 1 if lit > 0 else -1
                    pressure_strength = (1 - sat_degree) * 0.3
                    pressures[var] += pressure_strength * (target - np.tanh(self.var_values[var]))
        
        # Обновление значений
        damping = 0.97
        inertia = 0.1
        for var in range(1, self.n_vars + 1):
            pressure = np.tanh(pressures[var])
            self.var_values[var] = damping * self.var_values[var] + inertia * pressure
            self.var_values[var] = np.clip(self.var_values[var], -1, 1)
        
        # ДЕТЕКТОР UNSAT: анализ амплитуды вибраций
        current_amplitude = np.mean([self.jitter_amplitude[var] for var in range(1, self.n_vars + 1)])
        self.amplitude_history.append(current_amplitude)
        
        # Проверка на предельный цикл (пульсации)
        if len(self.amplitude_history) > 100:
            # Быстрое преобразование Фурье для поиска частоты
            amplitudes = np.array(self.amplitude_history)
            fft = np.fft.fft(amplitudes - np.mean(amplitudes))
            freqs = np.fft.fftfreq(len(amplitudes))
            
            # Ищем доминирующую частоту (исключая нулевую)
            magnitude = np.abs(fft)
            magnitude[0] = 0  # Игнорируем DC компоненту
            dominant_freq_idx = np.argmax(magnitude)
            dominant_freq = abs(freqs[dominant_freq_idx])
            
            # Проверяем, есть ли устойчивая пульсация (пульс раз в 3 оборота)
            expected_pulse_freq = 1.0 / (3 * 2 * np.pi / 0.1)  # Частота пульса
            
            if 0.01 < dominant_freq < 0.1 and np.std(amplitudes[-50:]) > 0.05:
                if not self.unsat_detected and current_amplitude > 0.1:
                    self.unsat_detected = True
                    self.cycle_frequency = dominant_freq
        
        # Вычисление RMS отклонения
        if len(self.history) > 20:
            recent_values = np.array(self.history[-20:])
            mean_values = np.mean(recent_values, axis=0)
            rms = np.sqrt(np.mean((self.var_values - mean_values)**2))
        else:
            rms = 1.0
        
        self.rms_history.append(rms)
        self.history.append(self.var_values.copy())
        
        # Ограничение истории
        max_history = 200
        if len(self.history) > max_history:
            self.history.pop(0)
        if len(self.rms_history) > max_history:
            self.rms_history.pop(0)
        
        # Проверка на решение
        if rms < 0.05 and not self.solution_found:
            satisfied = all(self.clause_satisfied(clause, self.var_values) 
                          for clause in self.clauses)
            if satisfied:
                self.solution_found = True
                self.solution_time = self.time
        
        return rms
    
    def draw_donut_with_gear_effect(self, ax, center_x, center_y, var_idx):
        """Отрисовка бублика с эффектом шестеренок и дребезгом"""
        
        # Применяем дребезг к позиции
        jitter_x = self.jitter_amplitude[var_idx] * 0.2 * np.cos(self.jitter_phase[var_idx] * 2)
        jitter_y = self.jitter_amplitude[var_idx] * 0.2 * np.sin(self.jitter_phase[var_idx] * 2)
        
        # Корректируем радиус с учетом дребезга
        current_radius = self.donut_radius * self.jitter_radius[var_idx]
        
        # Определяем цвет с учетом вспышки
        var_val = self.var_values[var_idx]
        if var_val > 0:
            base_color = plt.cm.RdYlGn(var_val)
        else:
            base_color = plt.cm.RdYlGn_r(abs(var_val))
        
        # Добавляем вспышку при конфликте
        flash = self.flash_intensity[var_idx]
        if flash > 0.1:
            # Смешиваем с белым
            color = tuple(min(1.0, c + flash) for c in base_color[:3])
        else:
            color = base_color
        
        # Внешний круг с эффектом шестеренок (зубчатый край)
        n_teeth = max(8, len(self.var_nodes.get(var_idx, [])) * 2)
        for i in range(n_teeth):
            angle = 2 * np.pi * i / n_teeth
            # Зубья шестеренки
            tooth_length = 0.1 if i % 2 == 0 else 0.05
            x1 = center_x + jitter_x + (current_radius - tooth_length) * np.cos(angle)
            y1 = center_y + jitter_y + (current_radius - tooth_length) * np.sin(angle)
            x2 = center_x + jitter_x + (current_radius + 0.1) * np.cos(angle)
            y2 = center_y + jitter_y + (current_radius + 0.1) * np.sin(angle)
            ax.plot([x1, x2], [y1, y2], 'k-', linewidth=1, alpha=0.3)
        
        # Основной круг
        outer_circle = Circle((center_x + jitter_x, center_y + jitter_y), 
                             current_radius, fill=False, color='black', linewidth=1.5)
        ax.add_patch(outer_circle)
        
        # Внутренний круг (дырка) - тоже вибрирует
        inner_circle = Circle((center_x + jitter_x, center_y + jitter_y), 
                             current_radius * 0.4, fill=False, 
                             color='black', linewidth=1.5, linestyle='--')
        ax.add_patch(inner_circle)
        
        # Заливка центра
        fill_circle = Circle((center_x + jitter_x, center_y + jitter_y), 
                            current_radius * 0.3, color=color, alpha=0.8, zorder=3)
        ax.add_patch(fill_circle)
        
        # Узлы (клаузы) с учетом дребезга
        if var_idx in self.var_nodes:
            for clause_idx, base_angle in self.var_nodes[var_idx]:
                # Учитываем вращение и дребезг
                angle = base_angle + self.var_phases[var_idx]
                
                # Позиция узла тоже вибрирует
                node_jitter = self.jitter_amplitude[var_idx] * 0.1
                x = center_x + jitter_x + current_radius * 0.7 * np.cos(angle) + node_jitter * np.cos(angle * 2)
                y = center_y + jitter_y + current_radius * 0.7 * np.sin(angle) + node_jitter * np.sin(angle * 2)
                
                # Цвет узла
                node_color = self.get_clause_color(clause_idx)
                
                # Размер узла зависит от удовлетворенности и дребезга
                sat_degree = self.get_clause_satisfaction_degree(
                    self.clauses[clause_idx], self.var_values)
                base_size = 0.1 + 0.1 * (1 - sat_degree)
                size = base_size * (1 + self.jitter_amplitude[var_idx])
                
                node = Circle((x, y), size, color=node_color, alpha=0.9, zorder=5)
                ax.add_patch(node)
                
                # Подсветка активного узла
                if abs(angle % (2*np.pi) - np.pi/2) < 0.3:
                    highlight = Circle((x, y), size + 0.05, color='yellow', 
                                     alpha=0.3 + self.flash_intensity[var_idx] * 0.3, zorder=4)
                    ax.add_patch(highlight)
        
        # Подпись переменной
        ax.text(center_x + jitter_x, center_y + jitter_y - current_radius - 0.4, 
               f'x{var_idx}', ha='center', va='top', fontsize=8, fontweight='bold')
        
        # ИНТЕГРАЛЬНЫЙ СЛЕД: маленькая осциллограмма боли под бубликом
        if var_idx in self.jitter_history and len(self.jitter_history[var_idx]) > 10:
            history = list(self.jitter_history[var_idx])[-30:]  # Последние 30 шагов
            if len(history) > 1:
                # Масштабируем и сдвигаем под бублик
                hist_x = np.linspace(center_x - 0.8, center_x + 0.8, len(history))
                hist_y = center_y - current_radius - 0.6 + np.array(history) * 0.3
                ax.plot(hist_x, hist_y, 'r-', linewidth=1, alpha=0.7)
                ax.fill_between(hist_x, center_y - current_radius - 0.6, hist_y, 
                               color='red', alpha=0.2)
        
        return outer_circle
    
    def animate(self, frame):
        """Функция анимации"""
        self.left_ax.clear()
        self.right_ax.clear()
        
        # Обновление динамики с эффектом шестеренок
        rms = self.update_dynamics_with_gear_effect()
        
        # Отрисовка бубликов
        for var in range(1, self.n_vars + 1):
            if var in self.donut_positions:
                x, y = self.donut_positions[var]
                self.draw_donut_with_gear_effect(self.left_ax, x, y, var)
        
        # Настройка левой панели
        grid_size = int(np.ceil(np.sqrt(self.n_vars)))
        margin = 3
        self.left_ax.set_xlim(-grid_size * 2 - margin, grid_size * 2 + margin)
        self.left_ax.set_ylim(-grid_size * 2 - margin, grid_size * 2 + margin)
        self.left_ax.set_aspect('equal')
        self.left_ax.axis('off')
        
        # Заголовок с информацией
        if self.unsat_detected:
            status = "⛔ UNSAT DETECTED: LIMIT CYCLE"
            status_color = 'red'
        elif self.solution_found:
            status = "✅ SAT: РЕШЕНИЕ НАЙДЕНО"
            status_color = 'green'
        else:
            status = "🔄 ПОИСК РЕШЕНИЯ"
            status_color = 'blue'
        
        self.left_ax.set_title(f'{self.benchmark_name}\n{status}', 
                              fontsize=12, fontweight='bold', color=status_color)
        
        # Легенда
        legend_x = -grid_size * 2 - margin + 0.5
        legend_y = grid_size * 2 + margin - 1
        self.left_ax.text(legend_x, legend_y, '● Horn', color='red', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 0.5, '● Dual-Horn', color='blue', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 1, '● XOR', color='green', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 1.5, '● Другие', color='gray', fontsize=10)
        
        # Информация о параметрах
        self.left_ax.text(legend_x, legend_y - 2.5, f'K={self.K}', fontsize=8)
        self.left_ax.text(legend_x, legend_y - 3, f'Амплитуда: {np.mean(self.jitter_amplitude[1:]):.3f}', 
                         fontsize=8)
        
        # График осцилляций
        if len(self.rms_history) > 1:
            times = np.arange(len(self.rms_history)) * 0.05
            
            self.right_ax.plot(times, self.rms_history, 'b-', linewidth=2, alpha=0.7, label='RMS')
            self.right_ax.fill_between(times, 0, self.rms_history, alpha=0.2)
            
            # Добавляем график амплитуды вибраций
            if len(self.amplitude_history) > 1:
                amp_times = np.arange(len(self.amplitude_history)) * 0.05
                self.right_ax.plot(amp_times, self.amplitude_history, 'r-', 
                                 linewidth=1.5, alpha=0.5, label='Дребезг')
            
            self.right_ax.set_xlabel('Время', fontsize=10)
            self.right_ax.set_ylabel('Амплитуда', fontsize=10)
            self.right_ax.set_title('Динамика системы', fontsize=12, fontweight='bold')
            self.right_ax.grid(True, alpha=0.3)
            self.right_ax.set_ylim(0, 1.5)
            self.right_ax.legend(loc='upper right', fontsize=8)
            
            # Отметки о состоянии
            if self.solution_found:
                self.right_ax.axhline(y=0.05, color='g', linestyle='--', alpha=0.5)
                self.right_ax.axvline(x=self.solution_time, color='g', linestyle='--', alpha=0.5)
                self.right_ax.text(0.5, 0.9, 'SAT', transform=self.right_ax.transAxes,
                                 ha='center', fontsize=14, color='green')
            elif self.unsat_detected:
                self.right_ax.axhline(y=0.3, color='r', linestyle='--', alpha=0.5)
                self.right_ax.text(0.5, 0.9, 'UNSAT (Limit Cycle)', transform=self.right_ax.transAxes,
                                 ha='center', fontsize=14, color='red')
        
        return self.left_ax, self.right_ax
    
    def run(self, interval=100):
        """Запуск анимации"""
        anim = FuncAnimation(self.fig, self.animate, interval=interval, blit=False, cache_frame_data=False)
        plt.tight_layout()
        plt.show()
        return anim


# ==================== MAIN ====================
def main():
    # Папка с бенчмарками
    bench_dir = "./benchmarks"
    Path(bench_dir).mkdir(exist_ok=True)
    
    print("="*70)
    print("🍩 ВИЗУАЛИЗАТОР SAT-ФОРМУЛЫ 'ВРАЩАЮЩИЕСЯ БУБЛИКИ'")
    print("⚙️  РЕЖИМ: ЭФФЕКТ ШЕСТЕРЕНОК + ФАЗОВЫЕ УДАРЫ")
    print("="*70)
    
    # Загружаем бенчмарки
    print(f"\nПоиск .cnf файлов в папке: {bench_dir}")
    benchmarks = load_benchmark_folder(bench_dir)
    
    if not benchmarks:
        print(f"\n❌ В папке {bench_dir} нет .cnf файлов!")
        print("\nСоздаю тестовую формулу с конфликтующей структурой...")
        
        # Создаем тестовую формулу, которая может привести к limit cycle
        test_file = os.path.join(bench_dir, "test_unsat.cnf")
        with open(test_file, 'w') as f:
            f.write('c Тестовая UNSAT формула (конфликтующая)\n')
            f.write('p cnf 4 8\n')
            # Противоречивая структура
            f.write('1 2 0\n')
            f.write('1 -2 0\n')
            f.write('-1 2 0\n')
            f.write('-1 -2 0\n')
            f.write('2 3 0\n')
            f.write('2 -3 0\n')
            f.write('-2 3 0\n')
            f.write('-2 -3 0\n')
        
        print(f"✅ Создан тестовый файл: {test_file}")
        benchmarks = load_benchmark_folder(bench_dir)
    
    # Выбираем случайный бенчмарк
    if benchmarks:
        print(f"\n📁 Найдено {len(benchmarks)} файлов")
        selected = random.choice(benchmarks)
        name, n, clauses = print_benchmark_info(selected)
        
        print(f"\n🚀 Запуск визуализации с эффектом шестеренок...")
        print("🔄 К=0.3, инерция зависит от числа узлов")
        print("🔄 Закройте окно для завершения программы")
        
        # Создаем и запускаем визуализатор
        viz = DonutSATVisualizer(n, clauses, name)
        viz.run(interval=100)
    else:
        print("❌ Не удалось загрузить бенчмарки")

if __name__ == "__main__":
    main()
