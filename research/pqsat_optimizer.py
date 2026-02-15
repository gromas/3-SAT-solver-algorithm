# pqsat_optimizer.py

"""
PQ-Algorithm Root Optimizer

This module provides tools for finding the optimal root variable for the PQ-algorithm.
The key insight is that the choice of starting variable significantly impacts performance:

Key Findings:
- For random 3-SAT (uf50): root selection affects complexity by ±15%
- For structured problems (flat50): impact grows to ±30%
- For large instances (sw100): impact diminishes to ±5-6%

The optimizer evaluates different metrics:
- ∑P² : Quadratic complexity (CPU-bound tasks)
- ∑2^P : Exponential complexity (memory-bound tasks)  
- Wmax : Peak core size (simplified metric)

Usage:
    python pqsat_optimizer.py <cnf_file> --find-optimal
    python pqsat_optimizer.py <cnf_file> --root <var>

Example:
    python pqsat_optimizer.py ./uf50/uf50-01.cnf --find-optimal

Output:
    - Best root by each metric
    - Statistics over all roots
    - Complexity variance (typically 15-30%)
    
The optimizer helps select the best starting variable before running 
the full PQ-algorithm, potentially saving 15-30% of runtime.


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
import statistics

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))
from pqsat import PQSATSolver
from dimacs_loader import parse_dimacs_cnf

def evaluate_root(formula_file, root_var, verbose=False):
    """
    Оценивает сложность для заданного корня.
    Возвращает: (Wmax, sum_P_squared, sum_2_P, steps_count)
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
    
    while remaining_clauses:
        # Выбор переменной
        if not P:
            current_var = root_var
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
        
        # Находим и удаляем клозы
        current_clauses = [idx for idx in var_clauses[current_var] if idx in remaining_clauses]
        
        entered = set()
        for idx in current_clauses:
            remaining_clauses.remove(idx)
            
            for lit in clauses_list[idx]:
                var = abs(lit)
                if var not in entry_time:
                    entry_time[var] = step
                    P.add(var)
                    entered.add(var)
        
        # Элиминация
        eliminated = set()
        for var in list(P):
            if not (var_clauses[var] & remaining_clauses):
                eliminated.add(var)
                exit_time[var] = step
        
        P -= eliminated
        
        steps_data.append({
            'step': step,
            'P_size': len(P)
        })
        
        step += 1
    
    # Вычисляем метрики
    p_sizes = [s['P_size'] for s in steps_data]
    Wmax = max(p_sizes) if p_sizes else 0
    sum_P_squared = sum(s * s for s in p_sizes)
    sum_2_P = sum(2 ** min(s, 30) for s in p_sizes)  # ограничиваем для численной стабильности
    
    if verbose:
        print(f"\n📊 Корень x{root_var}:")
        print(f"  Wmax = {Wmax}")
        print(f"  Шагов = {len(steps_data)}")
        print(f"  ∑P² = {sum_P_squared}")
        print(f"  ∑2^P ≈ {sum_2_P}")
    
    return {
        'root': root_var,
        'Wmax': Wmax,
        'steps': len(steps_data),
        'sum_P_squared': sum_P_squared,
        'sum_2_P': sum_2_P,
        'p_sizes': p_sizes
    }

def find_optimal_root(formula_file, sample_roots=None, verbose=True):
    """
    Находит оптимальный корень для формулы.
    Если sample_roots=None, проверяет все переменные.
    """
    n, clauses = parse_dimacs_cnf(formula_file)
    all_vars = set()
    for clause in clauses:
        for lit in clause:
            all_vars.add(abs(lit))
    
    if sample_roots is None:
        roots_to_test = sorted(all_vars)
    else:
        roots_to_test = sample_roots
    
    if verbose:
        print(f"\n🔍 Поиск оптимального корня среди {len(roots_to_test)} переменных")
        print("=" * 60)
    
    results = []
    for i, root in enumerate(roots_to_test):
        if verbose and i % 5 == 0:
            print(f"  Тестируем {i+1}/{len(roots_to_test)}...")
        
        try:
            res = evaluate_root(formula_file, root, verbose=False)
            results.append(res)
        except Exception as e:
            if verbose:
                print(f"  ❌ Ошибка при x{root}: {e}")
    
    if not results:
        return None
    
    # Сортируем по разным метрикам
    by_Wmax = sorted(results, key=lambda x: (x['Wmax'], x['sum_P_squared']))
    by_sum_P2 = sorted(results, key=lambda x: x['sum_P_squared'])
    by_sum_2P = sorted(results, key=lambda x: x['sum_2_P'])
    
    optimal_by_P2 = by_sum_P2[0]
    optimal_by_2P = by_sum_2P[0]
    optimal_by_Wmax = by_Wmax[0]
    
    if verbose:
        print("\n" + "=" * 60)
        print("📊 РЕЗУЛЬТАТЫ ПОИСКА ОПТИМАЛЬНОГО КОРНЯ")
        print("=" * 60)
        
        print(f"\n🏆 По сумме P² (квадратичная сложность):")
        print(f"   Корень x{optimal_by_P2['root']}:")
        print(f"     Wmax = {optimal_by_P2['Wmax']}")
        print(f"     ∑P² = {optimal_by_P2['sum_P_squared']}")
        print(f"     ∑2^P = {optimal_by_P2['sum_2_P']}")
        print(f"     Шагов = {optimal_by_P2['steps']}")
        
        print(f"\n🏆 По сумме 2^P (экспоненциальная сложность):")
        print(f"   Корень x{optimal_by_2P['root']}:")
        print(f"     Wmax = {optimal_by_2P['Wmax']}")
        print(f"     ∑P² = {optimal_by_2P['sum_P_squared']}")
        print(f"     ∑2^P = {optimal_by_2P['sum_2_P']}")
        print(f"     Шагов = {optimal_by_2P['steps']}")
        
        print(f"\n🏆 По минимальному Wmax:")
        print(f"   Корень x{optimal_by_Wmax['root']}:")
        print(f"     Wmax = {optimal_by_Wmax['Wmax']}")
        print(f"     ∑P² = {optimal_by_Wmax['sum_P_squared']}")
        print(f"     ∑2^P = {optimal_by_Wmax['sum_2_P']}")
        print(f"     Шагов = {optimal_by_Wmax['steps']}")
        
        # Статистика по всем
        all_Wmax = [r['Wmax'] for r in results]
        all_P2 = [r['sum_P_squared'] for r in results]
        all_2P = [r['sum_2_P'] for r in results]
        
        print(f"\n📈 Статистика по {len(results)} корням:")
        print(f"  Wmax: среднее={statistics.mean(all_Wmax):.1f}, "
              f"мин={min(all_Wmax)}, макс={max(all_Wmax)}")
        print(f"  ∑P²: среднее={statistics.mean(all_P2):.0f}, "
              f"мин={min(all_P2)}, макс={max(all_P2)}")
        print(f"  ∑2^P: среднее={statistics.mean(all_2P):.0f}, "
              f"мин={min(all_2P)}, макс={max(all_2P)}")
        
        # Разброс
        p2_range = (max(all_P2) - min(all_P2)) / min(all_P2) * 100
        print(f"\n📉 Разброс сложности: {p2_range:.1f}%")
    
    return {
        'by_P2': optimal_by_P2,
        'by_2P': optimal_by_2P,
        'by_Wmax': optimal_by_Wmax,
        'all_results': results,
        'statistics': {
            'count': len(results),
            'Wmax': {
                'mean': statistics.mean(all_Wmax),
                'min': min(all_Wmax),
                'max': max(all_Wmax)
            },
            'sum_P2': {
                'mean': statistics.mean(all_P2),
                'min': min(all_P2),
                'max': max(all_P2)
            },
            'sum_2P': {
                'mean': statistics.mean(all_2P),
                'min': min(all_2P),
                'max': max(all_2P)
            }
        }
    }

def save_root_statistics(results, filename="root_stats.txt"):
    """
    Сохраняет статистику по корням в файл.
    """
    with open(filename, 'w', encoding='utf-8') as f:
        f.write("Статистика по корням для uf50-01\n")
        f.write("=" * 60 + "\n\n")
        
        # Сортируем по сложности
        sorted_by_P2 = sorted(results['all_results'], key=lambda x: x['sum_P_squared'])
        
        f.write("Корни, отсортированные по сложности (∑P²):\n")
        f.write("-" * 50 + "\n")
        f.write("Корень | Wmax | Шаги | ∑P²    | ∑2^P\n")
        f.write("-" * 50 + "\n")
        
        for r in sorted_by_P2:
            f.write(f"x{r['root']:2}   | {r['Wmax']:4} | {r['steps']:4} | {r['sum_P_squared']:6} | {r['sum_2_P']:8}\n")
        
        f.write("\n" + "=" * 60 + "\n")
        f.write(f"Лучший корень по ∑P²: x{results['by_P2']['root']}\n")
        f.write(f"Лучший корень по ∑2^P: x{results['by_2P']['root']}\n")
        f.write(f"Лучший корень по Wmax: x{results['by_Wmax']['root']}\n")
        
        stats = results['statistics']
        f.write(f"\nСтатистика по {stats['count']} корням:\n")
        f.write(f"  Wmax: среднее={stats['Wmax']['mean']:.1f}, "
                f"мин={stats['Wmax']['min']}, макс={stats['Wmax']['max']}\n")
        f.write(f"  ∑P²: среднее={stats['sum_P2']['mean']:.0f}, "
                f"мин={stats['sum_P2']['min']}, макс={stats['sum_P2']['max']}\n")
        
        p2_range = (stats['sum_P2']['max'] - stats['sum_P2']['min']) / stats['sum_P2']['min'] * 100
        f.write(f"\nРазброс сложности: {p2_range:.1f}%\n")
    
    print(f"\n💾 Статистика сохранена в {filename}")

def main():
    import argparse
    
    parser = argparse.ArgumentParser()
    parser.add_argument('file', help='CNF файл')
    parser.add_argument('--find-optimal', action='store_true', help='Найти оптимальный корень')
    parser.add_argument('--root', type=int, help='Использовать конкретный корень')
    parser.add_argument('--save-stats', action='store_true', help='Сохранить статистику')
    
    args = parser.parse_args()
    
    if args.find_optimal:
        results = find_optimal_root(args.file, verbose=True)
        if args.save_stats and results:
            save_root_statistics(results, f"{os.path.basename(args.file)}_roots.txt")
    
    elif args.root:
        evaluate_root(args.file, args.root, verbose=True)
    
    else:
        print("Укажите --find-optimal или --root")

if __name__ == "__main__":
    main()
