package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Map;

public class TernaryExpr implements Expr {
    private List<Node> children;

    public TernaryExpr(Expr condition, Expr trueExpr, Expr falseExpr) {
        this.children = Lists.newArrayList(condition, trueExpr, falseExpr);
    }

    public Expr getCondition() {
        return (Expr) children.get(0);
    }

    public Expr getTrueExpr() {
        return (Expr) children.get(1);
    }

    public Expr getFalseExpr() {
        return (Expr) children.get(2);
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> vars) {
        return new TernaryExpr(
            getCondition().replace(vars),
            getTrueExpr().replace(vars),
            getFalseExpr().replace(vars));
    }
}
