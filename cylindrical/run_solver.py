#!/usr/bin/env python3
"""
Запуск 3-SAT солвера с механизмом рефрактерности.

Новые опции:
    --cooldown BASE    Базовая длительность охлаждения (по умолчанию: 5)
    --cooldown-var N   Вариативность охлаждения (по умолчанию: 2)
    --no-cooldown      Отключить механизм рефрактерности
"""

import os
import sys
import time
import argparse
import random
from pathlib import Path
import json
from datetime import datetime

from cylindrical_solver import CylinderSolver
from dimacs_loader import parse_dimacs_cnf, load_benchmark_folder, print_benchmark_info


def print_header():
    """Выводит заголовок."""
    print("\n" + "╔" + "═"*78 + "╗")
    print("║" + " "*30 + "🔮 ЦИЛИНДРИЧЕСКИЙ 3-SAT СОЛВЕР" + " "*30 + "║")
    print("║" + " "*25 + "Cylindrical Gravity Prototyper v1.1" + " "*26 + "║")
    print("║" + " "*30 + "✨ с рефрактерностью ✨" + " "*30 + "║")
    print("╚" + "═"*78 + "╝\n")


def print_result(sat, assignment, stats, elapsed, filename, args):
    """Выводит результат."""
    status = "✅ SAT" if sat else "❌ UNSAT (или таймаут)"
    
    print("\n" + "─"*80)
    print(f"📁 Файл: {filename}")
    print(f"📊 Статус: {status}")
    print(f"⏱️  Время: {elapsed:.2f} сек")
    print(f"📈 Шагов: {stats.get('steps', 0)}")
    
    if 'best_energy' in stats:
        print(f"⚡ Лучшая энергия: {stats['best_energy']} нарушенных клауз")
    
    if 'cooldown_stats' in stats:
        active, avg, max_cd = stats['cooldown_stats']
        print(f"🌡️ Cooldown stats: {active} в бане, средний {avg:.1f}, макс {max_cd}")
    
    if sat and not args.quiet:
        n_vars = len(assignment)
        print(f"\n📝 Присваивание (первые 20 из {n_vars}):")
        ass_str = []
        for i, val in enumerate(assignment[:20]):
            ass_str.append(f"x{i+1}={1 if val else 0}")
        print("  " + ", ".join(ass_str))
        if n_vars > 20:
            print(f"  ... и ещё {n_vars-20} переменных")
    
    print("─"*80)


def run_on_file(filename, args):
    """Запускает солвер на одном файле."""
    try:
        print(f"\n📂 Загрузка: {filename}")
        n_vars, clauses = parse_dimacs_cnf(str(filename))
        
        if n_vars == 0:
            print(f"⚠️  Предупреждение: в файле {filename} не найдено переменных")
            return False, [], {'error': 'no_vars'}, 0
        
        print(f"   Переменных: {n_vars}, Дизъюнктов: {len(clauses)}")
        print(f"   Плотность: {len(clauses)/n_vars:.2f}")
        
        # Настройка cooldown
        if args.no_cooldown:
            cooldown_base = 0
            cooldown_var = 0
        else:
            cooldown_base = args.cooldown
            cooldown_var = args.cooldown_var
        
        # Создаем солвер
        solver = CylinderSolver(
            n_vars, 
            clauses, 
            seed=args.seed,
            verbose=not args.quiet,
            cooldown_base=cooldown_base,
            cooldown_variance=cooldown_var
        )
        
        # Запускаем
        start_time = time.time()
        sat, assignment, stats = solver.solve(
            max_steps=args.max_steps,
            timeout=args.timeout,
            target_energy=0,
            verbose=not args.quiet
        )
        elapsed = time.time() - start_time
        
        stats['n_vars'] = n_vars
        stats['n_clauses'] = len(clauses)
        
        return sat, assignment, stats, elapsed
        
    except Exception as e:
        print(f"❌ Ошибка при обработке {filename}: {e}")
        return False, [], {'error': str(e)}, 0


def main():
    parser = argparse.ArgumentParser(
        description="Запуск 3-SAT солвера с рефрактерностью",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        'path',
        help='Путь к .cnf файлу или папке'
    )
    
    parser.add_argument(
        '--max-steps',
        type=int,
        default=10000,
        help='Максимальное количество шагов (по умолчанию: 10000)'
    )
    
    parser.add_argument(
        '--timeout',
        type=int,
        default=60,
        help='Таймаут в секундах (по умолчанию: 60)'
    )
    
    parser.add_argument(
        '--seed',
        type=int,
        default=None,
        help='Seed для воспроизводимости'
    )
    
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Тихий режим'
    )
    
    parser.add_argument(
        '--stats',
        action='store_true',
        help='Показать подробную статистику'
    )
    
    parser.add_argument(
        '--random',
        action='store_true',
        help='Выбрать случайный файл'
    )
    
    parser.add_argument(
        '--all',
        action='store_true',
        help='Запустить на всех файлах'
    )
    
    parser.add_argument(
        '--output',
        help='Сохранить результаты в JSON'
    )
    
    parser.add_argument(
        '--info',
        action='store_true',
        help='Показать информацию о файлах'
    )
    
    # Новые параметры для рефрактерности
    parser.add_argument(
        '--cooldown',
        type=int,
        default=5,
        help='Базовая длительность охлаждения (по умолчанию: 5)'
    )
    
    parser.add_argument(
        '--cooldown-var',
        type=int,
        default=2,
        help='Вариативность охлаждения (по умолчанию: 2)'
    )
    
    parser.add_argument(
        '--no-cooldown',
        action='store_true',
        help='Отключить механизм рефрактерности'
    )
    
    parser.add_argument(
        '--cool-down-factor',
        type=float,
        default=0.5,
        help='Фактор системного охлаждения (по умолчанию: 0.5)'
    )
    
    args = parser.parse_args()
    
    if args.seed is not None:
        random.seed(args.seed)
    
    if not args.quiet:
        print_header()
        if not args.no_cooldown:
            print(f"🌡️ Рефрактерность: base={args.cooldown}, var={args.cooldown_var}")
        else:
            print("⚠️ Рефрактерность отключена")
        print()
    
    path = Path(args.path)
    
    # Определяем файлы для запуска
    files_to_run = []
    
    if path.is_file() and path.suffix.lower() == '.cnf':
        files_to_run = [path]
    elif path.is_dir():
        if args.random:
            cnf_files = list(path.glob("*.cnf"))
            if cnf_files:
                files_to_run = [random.choice(cnf_files)]
            else:
                print(f"❌ В папке {path} нет .cnf файлов")
                return 1
        elif args.all:
            files_to_run = list(path.glob("*.cnf"))
            if not files_to_run:
                print(f"❌ В папке {path} нет .cnf файлов")
                return 1
        else:
            files_to_run = list(path.glob("*.cnf"))
            if not files_to_run:
                print(f"❌ В папке {path} нет .cnf файлов")
                return 1
    else:
        print(f"❌ Путь {path} не является .cnf файлом или папкой")
        return 1
    
    files_to_run.sort()
    
    if args.info:
        print(f"\n📋 Информация о {'файле' if len(files_to_run) == 1 else 'файлах'}:\n")
        for filepath in files_to_run:
            try:
                n_vars, clauses = parse_dimacs_cnf(str(filepath))
                print(f"📄 {filepath.name}:")
                print(f"   Переменных: {n_vars}")
                print(f"   Дизъюнктов: {len(clauses)}")
                print(f"   Плотность: {len(clauses)/max(1, n_vars):.2f}")
                
                if clauses:
                    lengths = [len(c) for c in clauses]
                    print(f"   Длины: min={min(lengths)}, max={max(lengths)}, "
                          f"среднее={sum(lengths)/len(lengths):.2f}")
                print()
            except Exception as e:
                print(f"❌ Ошибка чтения {filepath.name}: {e}")
        return 0
    
    # Запускаем
    results = {
        'timestamp': datetime.now().isoformat(),
        'args': vars(args),
        'results': []
    }
    
    total_start = time.time()
    
    for i, filepath in enumerate(files_to_run, 1):
        if len(files_to_run) > 1:
            print(f"\n{'='*80}")
            print(f"📌 Файл {i}/{len(files_to_run)}")
            print(f"{'='*80}")
        
        sat, assignment, stats, elapsed = run_on_file(str(filepath), args)
        
        if not args.quiet or args.stats:
            print_result(sat, assignment, stats, elapsed, filepath.name, args)
        
        result = {
            'file': str(filepath),
            'sat': sat,
            'elapsed': elapsed,
            'stats': stats
        }
        
        if sat:
            result['assignment_sample'] = assignment[:100]
            result['n_vars'] = len(assignment)
        
        results['results'].append(result)
        
        if len(files_to_run) > 1:
            remaining = len(files_to_run) - i
            elapsed_total = time.time() - total_start
            avg_time = elapsed_total / i
            est_remaining = avg_time * remaining
            print(f"\n📊 Прогресс: {i}/{len(files_to_run)} "
                  f"(осталось ~{est_remaining:.1f} сек)")
    
    if len(files_to_run) > 1:
        total_time = time.time() - total_start
        sat_count = sum(1 for r in results['results'] if r['sat'])
        
        print("\n" + "="*80)
        print("📊 ИТОГОВАЯ СТАТИСТИКА")
        print("="*80)
        print(f"Всего файлов: {len(files_to_run)}")
        print(f"SAT: {sat_count}")
        print(f"UNSAT/Timeout: {len(files_to_run) - sat_count}")
        print(f"Общее время: {total_time:.2f} сек")
        print(f"Среднее время на файл: {total_time/len(files_to_run):.2f} сек")
    
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        print(f"\n💾 Результаты сохранены в {args.output}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
