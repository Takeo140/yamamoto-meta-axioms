use std::collections::HashMap;

// ============================================================
// §1. Core Definitions & Structures
// ============================================================

/// 公理系が目指す成功ステートの定数
pub const SUCCESS: &str = "META_AXIOM_SUCCESS";

/// A4: Hierarchical Structure を表現するミクロノード
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MicroNode {
    pub weight: usize,
    pub value: String,
}

impl MicroNode {
    pub fn new(weight: usize, value: &str) -> Self {
        Self {
            weight,
            value: value.to_string(),
        }
    }
}

/// 高度化された MetaSystem
/// トポロジー写像は実数モデルとして `HashMap` を用いて表現
#[derive(Debug, Clone)]
pub struct MetaSystem {
    pub scale_n: usize,
    /// A1: ショートサーキット用のアトラクター（特異点）
    pub attractor: Option<String>,
    /// A2: Topological Space - キーからミクロ階層（Vector）へのトポロジー写像
    pub topology_map: HashMap<String, Vec<MicroNode>>,
}

// ============================================================
// §4. Execution & Extraction Logic (実装)
// ============================================================

impl MetaSystem {
    pub fn new(scale_n: usize, attractor: Option<String>, topology_map: HashMap<String, Vec<MicroNode>>) -> Self {
        Self {
            scale_n,
            attractor,
            topology_map,
        }
    }

    /// 実際の解抽出関数（アルゴリズムの仕様）
    /// 1. 特定のルートキー "system_root" ならハッシュ計算すらスキップ（ショートサーキット）
    /// 2. それ以外はトポロジーマップの先頭（最高重み）を一撃で確認。
    /// 
    /// 配列の先頭要素へのアクセス、およびHashMapのルックアップはO(1)で実行されます。
    pub fn extract_solution(&self, key: &str) -> Option<&str> {
        if key == "system_root" {
            // A1: アトラクターによる O(1) ショートサーキット
            self.attractor.as_deref()
        } else {
            // A2, A4: トポロジーマップのミクロ階層リストから先頭要素（最高優先度）を一撃で取得
            self.topology_map.get(key)?
                .first()
                .map(|node| node.value.as_str())
        }
    }

    /// 抽出された結果が SUCCESS であるかどうかを判定する述語
    pub fn is_extract_success(&self, key: &str) -> bool {
        self.extract_solution(key) == Some(SUCCESS)
    }
}

// ============================================================
// §5. Verification & Unit Tests (Leanの定理の具現化)
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean定理: `short_circuit_principle` の検証
    /// アトラクターにSUCCESSがあり、かつ "system_root" へのアクセスであれば、
    /// 他のマップの状態（たとえ空であっても）に関わらず一撃でSUCCESSが返る。
    #[test]
    fn test_short_circuit_principle() {
        let system = MetaSystem::new(
            10000, // 巨大なシステムスケール N
            Some(SUCCESS.to_string()), // hA1: A1_ExtremumPrinciple
            HashMap::new(), // トポロジー空間は空（バイパスされるため影響しない）
        );

        // 実行コスト O(1) での抽出をシミュレート
        assert!(system.is_extract_success("system_root"));
    }

    /// Lean定理: `O1_convergence` の検証
    /// トポロジー空間の該当キーの先頭（最高階層）に SUCCESS が配置されている場合、
    /// システムの規模 N や、後続のtail要素の長さに関わらず、1ステップ（O(1)）で SUCCESS が抽出される。
    #[test]
    fn test_o1_convergence() {
        let mut map = HashMap::new();
        
        // 公理A4（階層構造）に従い、重みの高い順（降順）にノードがソートされているバケット
        let bucket = vec![
            MicroNode::new(100, SUCCESS),        // head_node (h_succ: value = SUCCESS)
            MicroNode::new(50, "LOWER_PRIORITY"), // tail element 1
            MicroNode::new(10, "OTHER_DATA"),     // tail element 2
        ];
        map.insert("target_key".to_string(), bucket);

        let system = MetaSystem::new(
            999_999_999, // 非常に巨大な N (N-Independence)
            None,
            map,
        );

        // ルートキーではない通常のキーアクセスにおいて、O(1)で先頭からSUCCESSが抽出できる
        assert!(system.is_extract_success("target_key"));
    }
}
