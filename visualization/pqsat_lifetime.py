# visualization/pqsat_lifetime.py
"""
feat: pqsat_lifetime.py - core dynamics visualization

This tool visualizes how variables enter and exit the core during
PQ-algorithm execution. Key features:
- Timeline of variable activation (green dots) and elimination (red dots)
- Core size graph showing P(t) dynamics
- Root variable highlighting for comparison
- Integrated complexity estimation (∑P² and ∑2^P)
- Helps identify optimal root selection strategy

Usage: python lifetime.py <cnf_file> --root <var> [--output <file>]


If you use this algorithm in your research, please cite:

@misc{pq2025,
  author = {R.S.Golubin},
  title = {PQ-Algorithm: Structural Elimination for SAT},
  year = {2026},
  publisher = {GitHub},
  url = {https://github.com/gromas/pqsat}
}

"""

import os
import sys
import matplotlib.pyplot as plt
import numpy as np
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))
from pqsat import PQSATSolver
from dimacs_loader import parse_dimacs_cnf

def build_lifetime_final(formula_file, root_var, verbose=True):
    """
    Финальная версия с правильной группировкой элиминаций.
    """
    n, clauses = parse_dimacs_cnf(formula_file)
    clauses_list = clauses
    
    remaining_clauses = set(range(len(clauses_list)))
    
    var_clauses = defaultdict(set)
    for idx, clause in enumerate(clauses_list):
        for lit in clause:
            var = abs(lit)
            var_clauses[var].add(idx)
    
    entry_time = {}
    exit_time = {}
    
    P = set()
    step = 0
    steps_data = []
    
    # Словарь: для каждого корня, какие переменные с ним вошли
    root_groups = {}
    
    if verbose:
        print(f"\n🚀 Старт с корневой переменной x{root_var}")
    
    while remaining_clauses:
        if verbose:
            print(f"\n📌 Шаг {step}:")
        
        # Выбор переменной
        if not P:
            current_var = root_var
            if verbose:
                print(f"   Ядро пусто, берём x{current_var}")
        else:
            candidates = set()
            for idx in remaining_clauses:
                for lit in clauses_list[idx]:
                    candidates.add(abs(lit))
            
            best_var = None
            best_overlap = -1
            
            for var in candidates:
                overlap = 0
                for idx in var_clauses[var]:
                    if idx in remaining_clauses:
                        clause_vars = {abs(lit) for lit in clauses_list[idx]}
                        overlap += len(clause_vars & P)
                
                if overlap > best_overlap:
                    best_overlap = overlap
                    best_var = var
            
            current_var = best_var
            if verbose:
                print(f"   Выбрана x{current_var} (пересечение: {best_overlap})")
        
        # Находим и удаляем клозы
        current_clauses = [idx for idx in var_clauses[current_var] if idx in remaining_clauses]
        
        if verbose:
            print(f"   Найдено {len(current_clauses)} клозов")
        
        for idx in current_clauses:
            remaining_clauses.remove(idx)
        
        # Добавляем новые переменные
        entered = set()
        for idx in current_clauses:
            for lit in clauses_list[idx]:
                var = abs(lit)
                if var not in P and var not in entry_time:
                    entered.add(var)
                    entry_time[var] = step
                    P.add(var)
                    if verbose:
                        print(f"   ➕ x{var} вошла")
        
        # Запоминаем группу для этого корня
        if entered:
            root_groups[current_var] = entered.copy()
            root_groups[current_var].add(current_var)
        
        # Элиминируем на том же шаге
        # Но не сразу — соберём все, кто должен умереть с этим корнем
        to_eliminate = set()
        
        # Сначала сам корень
        if current_var in P:
            to_eliminate.add(current_var)
        
        # Проверяем, кто ещё может умереть
        for var in list(P):
            if not (var_clauses[var] & remaining_clauses):
                to_eliminate.add(var)
        
        # Если есть кого элиминировать
        if to_eliminate:
            if verbose:
                print(f"   🔜 Элиминация {len(to_eliminate)} переменных: x{sorted(to_eliminate)}")
            
            # Запоминаем для финальной группировки
            steps_data.append({
                'step': step,
                'entered': entered,
                'to_eliminate': to_eliminate.copy(),
                'current_var': current_var,
                'P_before': len(P),
                'P_after': len(P) - len(to_eliminate)
            })
            
            P -= to_eliminate
        else:
            steps_data.append({
                'step': step,
                'entered': entered,
                'to_eliminate': set(),
                'current_var': current_var,
                'P_before': len(P),
                'P_after': len(P)
            })
        
        step += 1
    
    # Фаза группировки элиминаций
    # Собираем всё в одном месте
    elimination_map = {}
    for s in steps_data:
        if s['to_eliminate']:
            # Все, кто должен элиминироваться на этом шаге
            for var in s['to_eliminate']:
                elimination_map[var] = s['step']
    
    # Проставляем времена выхода
    for var, elim_step in elimination_map.items():
        exit_time[var] = elim_step
    
    if verbose:
        print(f"\n✅ Завершено за {len(steps_data)} шагов")
        print(f"   Всего переменных: {len(entry_time)}")
        sizes = [s['P_after'] for s in steps_data]
        print(f"   Wmax = {max(sizes)}")
    
    return entry_time, exit_time, steps_data, root_groups

def plot_lifetime_final(formula_file, root_var, highlight_var=None):
    """
    Финальная визуализация.
    """
    entry_time, exit_time, steps, root_groups = build_lifetime_final(formula_file, root_var, verbose=True)
    
    all_vars = sorted(entry_time.keys(), key=lambda v: entry_time[v])
    var_to_y = {v: i for i, v in enumerate(all_vars)}
    
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(16, 10), 
                                    gridspec_kw={'height_ratios': [3, 1]})
    
    colors = plt.cm.tab20(np.linspace(0, 1, len(steps)))
    
    # Рисуем линии жизни
    for var in all_vars:
        start = entry_time[var]
        end = exit_time.get(var, start)
        y = var_to_y[var]
        
        # Находим индекс для отображения
        start_disp = start
        end_disp = end
        
        color = colors[start_disp % len(colors)]
        
        ax1.plot([start_disp, end_disp], [y, y], linewidth=2, color=color, alpha=0.7)
        ax1.scatter(start_disp, y, c='green', s=40, alpha=0.8, edgecolors='black', zorder=5)
        if var in exit_time:
            ax1.scatter(end_disp, y, c='red', s=40, alpha=0.8, edgecolors='black', zorder=5)
    
    # Подсветка корня
    if root_var in var_to_y:
        y = var_to_y[root_var]
        start = entry_time[root_var]
        end = exit_time.get(root_var, start)
        
        ax1.plot([start, end], [y, y], linewidth=4, color='blue', alpha=0.9,
                label=f'Корень x{root_var}')
        ax1.scatter(start, y, c='cyan', s=100, edgecolors='black', zorder=10)
        if root_var in exit_time:
            ax1.scatter(end, y, c='purple', s=100, edgecolors='black', zorder=10)
        
        # Подсвечиваем всю группу корня
        if root_var in root_groups:
            group = root_groups[root_var]
            for var in group:
                if var != root_var and var in var_to_y:
                    yg = var_to_y[var]
                    ax1.plot([entry_time[var], exit_time.get(var, entry_time[var])], 
                            [yg, yg], linewidth=1, color='lightblue', alpha=0.5)
    
    # Подсветка указанной переменной
    if highlight_var and highlight_var in var_to_y and highlight_var != root_var:
        y = var_to_y[highlight_var]
        start = entry_time[highlight_var]
        end = exit_time.get(highlight_var, start)
        
        ax1.plot([start, end], [y, y], linewidth=4, color='yellow', alpha=0.8,
                label=f'x{highlight_var}')
        ax1.scatter(start, y, c='yellow', s=100, edgecolors='black', zorder=10)
        if highlight_var in exit_time:
            ax1.scatter(end, y, c='orange', s=100, edgecolors='black', zorder=10)
    
    # Отметки шагов
    for i, s in enumerate(steps):
        ax1.axvline(x=i, color='gray', alpha=0.2, linewidth=1)
        
        if s['entered']:
            ax1.text(i, -2, f"⬆️{len(s['entered'])}", fontsize=8, ha='center')
        if s['to_eliminate']:
            ax1.text(i, -1, f"⬇️{len(s['to_eliminate'])}", fontsize=8, ha='center', color='red')
        
        ax1.text(i, -3, f'x{s["current_var"]}', fontsize=7, ha='center', rotation=45)
    
    ax1.set_xlabel('Шаг алгоритма')
    ax1.set_ylabel('Переменные')
    ax1.set_title(f'Жизненный цикл с группировкой элиминаций\n{os.path.basename(formula_file)}')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(-0.5, len(steps) - 0.5)
    ax1.set_ylim(-5, len(all_vars))
    ax1.legend(loc='upper right')
    
    # Размер ядра
    p_sizes = [s['P_after'] for s in steps]
    ax2.plot(range(len(steps)), p_sizes, 'b-', linewidth=2, marker='o')
    ax2.fill_between(range(len(steps)), p_sizes, alpha=0.3, color='blue')
    ax2.set_xlabel('Шаг')
    ax2.set_ylabel('Размер ядра')
    ax2.set_title('Активные переменные')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(-0.5, len(steps) - 0.5)
    
    Wmax = max(p_sizes)
    ax2.axhline(y=Wmax, color='red', linestyle='--', linewidth=2, label=f'Wmax = {Wmax}')
    ax2.legend()
    
    print(f"\n📊 Статистика:")
    print(f"  Шагов: {len(steps)}")
    print(f"  Переменных: {len(all_vars)}")
    print(f"  Wmax = {Wmax}")
    print(f"  Групп корней: {len(root_groups)}")
    
    plt.tight_layout()
    return fig

def main():
    import argparse
    
    parser = argparse.ArgumentParser()
    parser.add_argument('file', help='CNF файл')
    parser.add_argument('--root', type=int, required=True, help='Корневая переменная')
    parser.add_argument('--var', type=int, help='Подсветить переменную')
    parser.add_argument('--output', help='Сохранить в файл')
    
    args = parser.parse_args()
    
    fig = plot_lifetime_final(args.file, args.root, args.var)
    
    if args.output:
        fig.savefig(args.output, dpi=150, bbox_inches='tight')
        print(f"Сохранено в {args.output}")
    else:
        plt.show()

if __name__ == "__main__":
    main()
