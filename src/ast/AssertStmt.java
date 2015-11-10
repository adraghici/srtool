package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class AssertStmt implements Node {
    private final Expr expr;

    public AssertStmt(Expr expr) {
        this.expr = expr;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
