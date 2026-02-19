import os
import time
import glob
from pq_functional_vacuum import PQFunctionalVacuum
from dimacs_loader import parse_dimacs_cnf

def run_test_on_file(file_path):
    print(f"\n{'='*60}")
    print(f"Файл: {os.path.basename(file_path)}")
    
    #with open(file_path, 'r') as f:
    #    content = f.read()
    
    try:
        vars_count, clauses = parse_dimacs_cnf(file_path)
        if vars_count == 0:
            print("Ошибка: Не удалось распарсить переменные (p cnf N M)")
            return
            
        solver = PQFunctionalVacuum(vars_count, clauses)
        
        start_time = time.time()
        result = solver.solve()
        end_time = time.time()
        
        duration = end_time - start_time
        status = "УСПЕХ" if (("uuf" in file_path and result == "UNSAT") or 
                            ("uf" in file_path and result == "SAT")) else "ПРОВЕРКА"
        
        print(f"{'-'*60}")
        print(f"РЕЗУЛЬТАТ: {result} | ВРЕМЯ: {duration:.4f}s | СТАТУС: {status}")
        
    except Exception as e:
        print(f"Критическая ошибка при обработке: {e}")

def main():
    # Путь к папке с бенчмарками (подправь под себя)
    # По умолчанию ищем в текущей папке все .cnf файлы
    benchmark_dir = "./benchmarks/" 
    
    # Если папки нет, берем текущую
    if not os.path.exists(benchmark_dir):
        benchmark_dir = "./"
        
    files = glob.glob(os.path.join(benchmark_dir, "*.cnf"))
    
    if not files:
        print(f"Файлы .cnf не найдены в {os.path.abspath(benchmark_dir)}")
        return

    # Сортируем файлы для удобства (сначала легкие)
    files.sort(key=lambda x: os.path.getsize(x))

    print(f"Найдено файлов для теста: {len(files)}")
    
    for f in files:
        run_test_on_file(f)

if __name__ == "__main__":
    main()
