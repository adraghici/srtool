package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class TernaryExpr implements Expr {
    private final Expr condition;
    private final Expr trueExpr;
    private final Expr falseExpr;

    public TernaryExpr(Expr condition, Expr trueExpr, Expr falseExpr) {
        this.condition = condition;
        this.trueExpr = trueExpr;
        this.falseExpr = falseExpr;
    }

    public Expr getCondition() {
        return condition;
    }

    public Expr getTrueExpr() {
        return trueExpr;
    }

    public Expr getFalseExpr() {
        return falseExpr;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(condition, trueExpr, falseExpr);
    }
}
