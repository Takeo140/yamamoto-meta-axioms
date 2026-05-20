import random

def collatz_sequence(n: int) -> list:
    """
    指定された初期値から1に収束するまでのコラッツ遷移（軌道）を計算する関数
    """
    if n <= 0:
        raise ValueError("初期値は1以上の整数を指定してください。")
        
    trajectory = [n]
    
    # 1に収束するまでデジタル演算を繰り返す
    while n > 1:
        if n % 2 == 0:
            # 最下位ビットが0（偶数）：右に1ビットシフト（/2）
            n = n // 2
        else:
            # 最下位ビットが1（奇数）：左シフトして元の値を足し、1を加える（3n+1）
            n = 3 * n + 1
        trajectory.append(n)
        
    return trajectory

def analyze_collatz(initial_value: int):
    """
    コラッツ演算のプロセスとその桁数（ビット長）の変化を表示する関数
    """
    sequence = collatz_sequence(initial_value)
    
    print(f"=== コラッツ・コンピューティング解析 ===")
    print(f"自動生成された初期値: {initial_value}")
    print(f"総ステップ数（収束まで）: {len(sequence) - 1} ステップ")
    print(f"最大到達値: {max(sequence)} (ビット長: {max(sequence).bit_length()} bit)")
    print("-" * 50)
    
    # 各ステップのデジタル状態を表示
    print(f"{'Step':<6} | {'現在の値 (10進数)':<22} | {'現在のビット長':<14}")
    print("-" * 50)
    
    for step, val in enumerate(sequence):
        # 最初の10ステップと、最後の5ステップ、および最大値の周辺のみをサンプル表示（長大化防止）
        if step < 10 or step > len(sequence) - 6 or val == max(sequence):
            print(f"{step:<6} | {val:<22} | {val.bit_length():>3} bit")
        elif step == 10:
            print(f"  ...  | {'（中略）':<22} |")

# --- 実行例（ランダム生成） ---
if __name__ == "__main__":
    # 1 から 100,000 の間でランダムな整数を1つ選ぶ
    # （より巨大な計算テストをしたい場合は、100000の桁を増やしてください）
    random_value = random.randint(1, 100000)
    
    analyze_collatz(random_value)
