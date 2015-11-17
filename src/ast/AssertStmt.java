package ast;

import visitor.Visitor;

public class AssertStmt implements Condition, Stmt {
    private final Expr condition;

    public AssertStmt(Expr condition) {
        this.condition = condition;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
