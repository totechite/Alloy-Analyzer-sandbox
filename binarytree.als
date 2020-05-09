// 二分木

sig Tree {root : lone Node}
sig Node {
    left, right : lone Node,
    key: one Int
}

// ~ は転置を意味する
// examples:
// ~(A -> B) = (B -> A)
// ~(parent -> child) = (child -> parent)
fun parent [] : Node->Node { ~(left + right) }

pred main{
    // 全てのNodeは次の性質を持つ | Node.leftとrightは異なる
    all n: Node | n.(left+right) != none implies n.left != n.right
    // n.left != n.right は φ != φ を含む為、終端Nodeを表現できない。
    // その為、終端Nodeへの性質の適用を回避する条件制約 n.(left+right) != φ implies { expr } を記述する

    // 次の性質を持つNodeは存在しない | あるNodeの親Nodeにそれ自身が含まれる
    no n: Node | n in n.^parent

    // 全てのNodeは次の性質を持つ | rootである or 一つの親Nodeを持つ　のいずれか
    all n : Node | (some t: Tree | t.root = n and no n.parent) or one n.parent

    // 各Nodeはkeyはユニークであること
    all disj n, n': Node | n.key != n'.key

    // Nodeは順序性があること
    // "n.left implies {expr} " は、この場合'if(n.left!=φ){expr}'のような認識でよさそう.
    all n: Node | some n.left implies all child: n.left.^(left+right) + n.left | child.key < n.key
    all n: Node | some n.right implies all child: n.right.^(left+right) + n.right | child.key > n.key
	
    all k: Node.key | k >= 0

    // バランス木であること
    // 差は１まで許される
    all n: Node | #n.left.^(left+right) <= #n.right.^(left+right) + 1.div[2]
    all n: Node | #n.right.^(left+right) <= #n.left.^(left+right) + 1.div[2]
}

run main for 3 but exactly 7 Node, exactly 1 Tree