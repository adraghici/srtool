package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class TernaryExpr implements Expr {
    private final Expr condition;
    private final Expr trueExpr;
    private final Expr falseExpr;
    private final List<Node> children;

    public TernaryExpr(Expr condition, Expr trueExpr, Expr falseExpr) {
        this.condition = condition;
        this.trueExpr = trueExpr;
        this.falseExpr = falseExpr;
        this.children = Lists.newArrayList(condition, trueExpr, falseExpr);
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
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
