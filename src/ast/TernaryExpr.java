package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class TernaryExpr implements Expr {
    private final Expr condition;
    private final Expr trueExpr;
    private final Expr falseExpr;

    public TernaryExpr(Expr condition, Expr trueExpr, Expr falseExpr) {
        this.condition = condition;
        this.trueExpr = trueExpr;
        this.falseExpr = falseExpr;
    }

    private Expr getCondition() {
        return condition;
    }

    private Expr getTrueExpr() {
        return trueExpr;
    }

    private Expr getFalseExpr() {
        return falseExpr;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(condition, trueExpr, falseExpr);
    }
}
