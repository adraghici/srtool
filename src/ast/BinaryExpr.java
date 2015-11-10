package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class BinaryExpr implements Expr {
    private final Expr condition;
    private final UnaryExpr left;
    private final UnaryExpr right;

    private BinaryExpr(Expr condition, UnaryExpr left, UnaryExpr right) {
        this.condition = condition;
        this.left = left;
        this.right = right;
    }

    private Expr getCondition() {
        return condition;
    }

    private UnaryExpr getLeft() {
        return left;
    }

    private UnaryExpr getRight() {
        return right;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(condition, left, right);
    }
}
