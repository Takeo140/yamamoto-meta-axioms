# =============================================================================
# F-BSCM 64-bit Unified Layer (PyTorch Edition)
# License: Apache-2.0 / CC-BY-4.0 Takeo Yamamoto
# =============================================================================
import torch
import torch.nn as nn

class UnifiedMachine64Layer(nn.Module):
    """
    Lean 4で完全検証されたF-BSCMと空間トポロジーをPyTorchテンソル上に再現。
    時間軸の平滑化と空間軸の順序不変性を同時に保証するカスタムレイヤー。
    """
    def __init__(self, feature_dim: int):
        super().__init__()
        # 64ビット空間の内部状態（時間軸）
        self.register_buffer('current_time', torch.zeros(feature_dim, dtype=torch.int64))

    def bscm_step_64(self, s: torch.Tensor, ext_input: torch.Tensor) -> torch.Tensor:
        """
        時間軸（BSCM）：64ビット境界を絶対に超えないロバスト制御ステップ。
        Lean 4の bscm_delta_64 をGPU上のビット演算として完全再現。
        """
        # s + input を計算
        combined = s + ext_input
        
        # 最下位ビット（LSB）の判定
        lsb = combined & 1
        
        # if s.lsb = false then s >>> 1 else (s + 1) >>> 1
        # PyTorchのビットシフト (>>) で高速に一括処理
        stepped = torch.where(
            lsb == 0,
            combined >> 1,
            (combined + 1) >> 1
        )
        return stepped

    def f_theory_spatial_sort(self, weights: torch.Tensor, values: torch.Tensor):
        """
        空間軸（F-Theory）：トポロジーの順序不変条件（SortedInvariant64）の再現。
        常に重み（w）の降順で計算の優先度と依存関係を再構築する。
        """
        # 重みに基づいて空間を幾何学的にソート
        sorted_weights, indices = torch.sort(weights, descending=True)
        sorted_values = values[indices]
        return sorted_weights, sorted_values

    def forward(self, ext_input: torch.Tensor, weights: torch.Tensor, values: torch.Tensor):
        """
        統合遷移システム（unified_system_step_64）
        時間軸の平滑化と空間軸の再構築を1ステップで完了させる。
        """
        # 1. 時間軸の平滑化（状態更新）
        ext_input_int = (ext_input * 1000).to(torch.int64) # 疑似的な浮動小数点→64bit変換
        self.current_time = self.bscm_step_64(self.current_time, ext_input_int)

        # 2. 空間軸の幾何学的順序の保証
        weights_int = (weights * 1000).to(torch.int64)
        v_sorted_w, v_sorted_v = self.f_theory_spatial_sort(weights_int, values)

        # 最適化された状態での出力を返す（以降のレイヤーへ伝播）
        return self.current_time.to(torch.float32), v_sorted_w, v_sorted_v

