#include <stdint.h>
#include <stdbool.h>

/**
 * @brief BSCMシステムの状態を保持する構造体 (定数空間 O(1))
 */
typedef struct {
    uint64_t current_state;
    bool is_halted;
} BSCM_System;

/**
 * @brief BSCMシステムの初期化
 * @param system 初期化対象のシステム構造体へのポインタ
 * @param initial_state 任意の64ビット初期状態
 */
void bscm_init(BSCM_System *system, uint64_t initial_state) {
    if (system == NULL) return;
    
    // 初期値が0であっても1であっても安全にハンドリング
    system->current_state = (initial_state == 0) ? 1 : initial_state;
    system->is_halted = (system->current_state == 1);
}

/**
 * @brief BSCMコア遷移関数 δ (定数時間 O(1))
 * * どのような破壊的入力(external_input)が飛び込んできても、
 * 絶対にオーバーフローやパニックを起こさず、情報を単調減少（縮退）させます。
 */
void bscm_step(BSCM_System *system, uint64_t external_input) {
    if (system == NULL || system->is_halted) return;

    // 1. 外部入力のカオスビットを安全に結合 (ラップアラウンド加算)
    // どんな巨大な値が来ても、C言語仕様上の未定義動作(UB)を起こさない符号なし安全加算
    uint64_t s = system->current_state + external_input;

    // 2. 状態遷移の分岐 (コラッツ構造の平滑化・外科手術)
    if (s % 2 == 0) {
        // 偶数：1ビット右シフト
        system->current_state = s >> 1;
    } else {
        // 奇数：(s >> 1) + 1 の等価変形により、u64::MAX時でも絶対にオーバーフローしない
        // オリジナルの「3x+1」のような爆発を構造的に絶滅
        system->current_state = (s >> 1) + 1;
    }

    // 3. 終了条件（唯一の不動点 1 への着陸チェック）
    if (system->current_state <= 1) {
        system->current_state = 1;
        system->is_halted = true;
    }
}

/**
 * @brief 外部割り込み・DoSフィルター用ラッパー（最大64ステップで必ず1に収束）
 * * 国家級サイバー攻撃（大量のDoSパケット）を浴びても、
 * この関数全体の最悪実行時間は完全に一定であり、システムを絶対にハングアップさせません。
 */
uint64_t bscm_process_until_halt(uint64_t initial_state, uint64_t external_input) {
    BSCM_System system;
    bscm_init(&system, initial_state);

    // 理論上、64ビット空間では最大64回（線形時間）のループで1に収束する
    // 万が一のハードウェアビット反転に備え、静的な上限付きループ（無限ループの物理的排除）
    for (int i = 0; i < 64; i++) {
        if (system.is_halted) {
            break;
        }
        bscm_step(&system, external_input);
        
        // 1ステップ処理した後は、次のステップでは外部入力を0として
        // 純粋な縮退（収束）フェーズへ移行させる（ノイズの減衰構造）
        external_input = 0;
    }

    return system.current_state; // どのような初期値からも、必ず「1」が返る
}
