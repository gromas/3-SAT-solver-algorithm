import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.patches import Circle
from collections import defaultdict
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

# ==================== DONUT SAT VISUALIZER ====================
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
        
        # Построение индексов
        for idx, clause in enumerate(self.clauses):
            for lit in clause:
                var = abs(lit)
                if 1 <= var <= n_vars:
                    self.var_to_clauses[var].append(idx)
        
        self.classify_clauses()
        
        # Параметры симуляции
        self.var_values = np.random.uniform(-1, 1, self.n_vars + 1)  # Индекс 0 не используется
        self.var_phases = np.random.uniform(0, 2*np.pi, self.n_vars + 1)
        self.time = 0
        self.history = []
        self.rms_history = []
        
        # Создание структуры узлов для каждой переменной
        self.build_variable_nodes()
        
        # Параметры визуализации
        self.fig = plt.figure(figsize=(16, 9))
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
        """Построение узлов для каждой переменной"""
        self.var_nodes = {}
        for var in range(1, self.n_vars + 1):
            clauses_for_var = self.var_to_clauses.get(var, [])
            if clauses_for_var:
                # Сортируем для стабильности
                clauses_for_var.sort()
                angles = np.linspace(0, 2*np.pi, len(clauses_for_var), endpoint=False)
                self.var_nodes[var] = list(zip(clauses_for_var, angles))
    
    def setup_visualization(self):
        """Настройка визуализации"""
        # Позиции для бубликов (сетка)
        grid_size = int(np.ceil(np.sqrt(self.n_vars)))
        for var in range(1, self.n_vars + 1):
            row = (var - 1) // grid_size
            col = (var - 1) % grid_size
            # Центрируем сетку
            x = col * 3 - (grid_size - 1) * 1.5
            y = -row * 3 + (grid_size - 1) * 1.5
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
    
    def update_dynamics(self):
        """Обновление динамики системы"""
        self.time += 0.05
        
        # Давление от клауз на переменные
        pressures = np.zeros(self.n_vars + 1)
        
        for clause_idx, clause in enumerate(self.clauses):
            sat_degree = self.get_clause_satisfaction_degree(clause, self.var_values)
            
            # Давление обратно пропорционально удовлетворению
            if sat_degree < 0.8:  # Клауза плохо удовлетворена
                for lit in clause:
                    var = abs(lit)
                    if var > self.n_vars:
                        continue
                    # Направление давления
                    target = 1 if lit > 0 else -1
                    # Сила давления зависит от неудовлетворенности
                    pressure_strength = (1 - sat_degree) * 0.3
                    pressures[var] += pressure_strength * (target - np.tanh(self.var_values[var]))
        
        # Влияние вращения узлов
        for var in range(1, self.n_vars + 1):
            # Вращение фазы
            self.var_phases[var] += 0.1
            
            # Давление от активного узла
            if var in self.var_nodes:
                nodes = self.var_nodes[var]
                if nodes:
                    # Находим узел в верхней позиции (угол близкий к 90°)
                    angles = [angle for _, angle in nodes]
                    # Учитываем вращение
                    rotated_angles = [(angle + self.var_phases[var]) % (2*np.pi) for angle in angles]
                    # Находим индекс ближайшего к верхней точке (π/2)
                    active_idx = min(range(len(rotated_angles)), 
                                   key=lambda i: abs(rotated_angles[i] - np.pi/2))
                    clause_idx, _ = nodes[active_idx]
                    
                    # Дополнительное давление от активной клаузы
                    if not self.clause_satisfied(self.clauses[clause_idx], self.var_values):
                        for lit in self.clauses[clause_idx]:
                            if abs(lit) == var:
                                target = 1 if lit > 0 else -1
                                pressures[var] += 0.2 * (target - np.tanh(self.var_values[var]))
        
        # Обновление значений переменных с учетом инерции и затухания
        damping = 0.97
        inertia = 0.1
        
        for var in range(1, self.n_vars + 1):
            # Нелинейное преобразование давления
            pressure = np.tanh(pressures[var])
            self.var_values[var] = damping * self.var_values[var] + inertia * pressure
            # Ограничение значений
            self.var_values[var] = np.clip(self.var_values[var], -1, 1)
        
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
            # Проверяем выполнимость
            satisfied = all(self.clause_satisfied(clause, self.var_values) 
                          for clause in self.clauses)
            if satisfied:
                self.solution_found = True
                self.solution_time = self.time
        
        return rms
    
    def draw_donut(self, ax, center_x, center_y, var_idx):
        """Отрисовка бублика для переменной"""
        # Внешний круг
        outer_circle = Circle((center_x, center_y), self.donut_radius, 
                             fill=False, color='black', linewidth=1.5)
        ax.add_patch(outer_circle)
        
        # Внутренний круг (дырка)
        inner_circle = Circle((center_x, center_y), self.donut_radius * 0.4, 
                             fill=False, color='black', linewidth=1.5, linestyle='--')
        ax.add_patch(inner_circle)
        
        # Значение переменной (заливка)
        var_val = self.var_values[var_idx]
        if var_val > 0:
            color = plt.cm.RdYlGn(var_val)
        else:
            color = plt.cm.RdYlGn_r(abs(var_val))
        
        fill_circle = Circle((center_x, center_y), self.donut_radius * 0.3, 
                            color=color, alpha=0.8, zorder=3)
        ax.add_patch(fill_circle)
        
        # Узлы (клаузы)
        if var_idx in self.var_nodes:
            for clause_idx, base_angle in self.var_nodes[var_idx]:
                # Учитываем вращение
                angle = base_angle + self.var_phases[var_idx]
                x = center_x + self.donut_radius * 0.7 * np.cos(angle)
                y = center_y + self.donut_radius * 0.7 * np.sin(angle)
                
                # Цвет узла по типу клаузы
                color = self.get_clause_color(clause_idx)
                
                # Размер узла зависит от удовлетворенности клаузы
                sat_degree = self.get_clause_satisfaction_degree(
                    self.clauses[clause_idx], self.var_values)
                size = 0.1 + 0.1 * (1 - sat_degree)
                
                node = Circle((x, y), size, color=color, alpha=0.9, zorder=5)
                ax.add_patch(node)
                
                # Подсветка активного узла (близкого к верхней точке)
                if abs(angle % (2*np.pi) - np.pi/2) < 0.3:
                    highlight = Circle((x, y), size + 0.05, color='yellow', 
                                     alpha=0.3, zorder=4)
                    ax.add_patch(highlight)
        
        # Подпись переменной
        ax.text(center_x, center_y - self.donut_radius - 0.3, f'x{var_idx}', 
               ha='center', va='top', fontsize=8, fontweight='bold')
        
        return outer_circle
    
    def animate(self, frame):
        """Функция анимации"""
        self.left_ax.clear()
        self.right_ax.clear()
        
        # Обновление динамики
        rms = self.update_dynamics()
        
        # Отрисовка бубликов
        for var in range(1, self.n_vars + 1):
            if var in self.donut_positions:
                x, y = self.donut_positions[var]
                self.draw_donut(self.left_ax, x, y, var)
        
        # Настройка левой панели
        grid_size = int(np.ceil(np.sqrt(self.n_vars)))
        margin = 2
        self.left_ax.set_xlim(-grid_size * 1.5 - margin, grid_size * 1.5 + margin)
        self.left_ax.set_ylim(-grid_size * 1.5 - margin, grid_size * 1.5 + margin)
        self.left_ax.set_aspect('equal')
        self.left_ax.axis('off')
        
        # Заголовок с информацией
        status = "✅ РЕШЕНИЕ" if self.solution_found else "🔄 ПОИСК"
        self.left_ax.set_title(f'{self.benchmark_name}\n{status} | t={self.time:.1f}', 
                              fontsize=12, fontweight='bold')
        
        # Легенда типов клауз
        legend_x = -grid_size * 1.5 - margin + 0.5
        legend_y = grid_size * 1.5 + margin - 1
        self.left_ax.text(legend_x, legend_y, '● Horn', color='red', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 0.5, '● Dual-Horn', color='blue', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 1, '● XOR', color='green', fontsize=10)
        self.left_ax.text(legend_x, legend_y - 1.5, '● Другие', color='gray', fontsize=10)
        
        # График осцилляций
        if len(self.rms_history) > 1:
            times = np.arange(len(self.rms_history)) * 0.05
            
            self.right_ax.plot(times, self.rms_history, 'b-', linewidth=2, alpha=0.7)
            self.right_ax.fill_between(times, 0, self.rms_history, alpha=0.2)
            
            # Сглаженная линия
            if len(self.rms_history) > 10:
                kernel = np.ones(5)/5
                smoothed = np.convolve(self.rms_history, kernel, mode='same')
                self.right_ax.plot(times, smoothed, 'r--', linewidth=1.5, alpha=0.5)
            
            self.right_ax.set_xlabel('Время', fontsize=10)
            self.right_ax.set_ylabel('RMS осцилляций', fontsize=10)
            self.right_ax.set_title('Динамика синхронизации', fontsize=12, fontweight='bold')
            self.right_ax.grid(True, alpha=0.3)
            self.right_ax.set_ylim(0, 1.1)
            
            # Отметка о решении
            if self.solution_found:
                self.right_ax.axhline(y=0.05, color='g', linestyle='--', alpha=0.5)
                self.right_ax.axvline(x=self.solution_time, color='g', linestyle='--', alpha=0.5)
                self.right_ax.text(0.5, 0.9, 'РЕШЕНИЕ НАЙДЕНО!', 
                                 transform=self.right_ax.transAxes,
                                 ha='center', fontsize=14, color='green', 
                                 bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
        
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
    
    print("="*60)
    print("🍩 ВИЗУАЛИЗАТОР SAT-ФОРМУЛЫ 'ВРАЩАЮЩИЕСЯ БУБЛИКИ'")
    print("="*60)
    
    # Загружаем бенчмарки
    print(f"\nПоиск .cnf файлов в папке: {bench_dir}")
    benchmarks = load_benchmark_folder(bench_dir)
    
    if not benchmarks:
        print(f"\n❌ В папке {bench_dir} нет .cnf файлов!")
        print("\nСоздаю тестовую формулу...")
        
        # Создаем тестовую формулу
        test_file = os.path.join(bench_dir, "test_formula.cnf")
        with open(test_file, 'w') as f:
            f.write('c Тестовая SAT формула\n')
            f.write('p cnf 6 12\n')
            # Horn клаузы
            f.write('1 -2 0\n')
            f.write('-1 -3 4 0\n')
            f.write('2 -4 0\n')
            f.write('3 -5 0\n')
            # Dual-Horn клаузы
            f.write('-1 -2 -3 0\n')
            f.write('-4 -5 -6 0\n')
            # XOR-подобные
            f.write('1 2 3 0\n')
            f.write('-1 -2 3 0\n')
            f.write('1 -2 -3 0\n')
            f.write('-1 2 -3 0\n')
            f.write('4 5 6 0\n')
            f.write('-4 -5 6 0\n')
        
        print(f"✅ Создан тестовый файл: {test_file}")
        benchmarks = load_benchmark_folder(bench_dir)
    
    # Выбираем случайный бенчмарк
    if benchmarks:
        print(f"\n📁 Найдено {len(benchmarks)} файлов")
        selected = random.choice(benchmarks)
        name, n, clauses = print_benchmark_info(selected)
        
        print(f"\n🚀 Запуск визуализации...")
        print("🔄 Закройте окно для завершения программы")
        
        # Создаем и запускаем визуализатор
        viz = DonutSATVisualizer(n, clauses, name)
        viz.run(interval=100)
    else:
        print("❌ Не удалось загрузить бенчмарки")

if __name__ == "__main__":
    main()
