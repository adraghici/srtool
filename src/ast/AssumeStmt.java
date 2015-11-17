package ast;

import visitor.Visitor;

public class AssumeStmt implements Condition, Stmt {
    private final Expr condition;

    public AssumeStmt(Expr condition) {
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
