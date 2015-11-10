package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class ParenExpr implements AtomExpr {
    private final Expr expr;

    public ParenExpr(Expr expr) {
        this.expr = expr;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(expr);
    }
}
