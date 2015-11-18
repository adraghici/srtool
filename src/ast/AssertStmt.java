package ast;

import visitor.Visitor;

public class AssertStmt implements Condition, Stmt {
    private final Expr condition;
    private final AssertStmt original;

    public AssertStmt(Expr condition, AssertStmt original) {
        this.condition = condition;
        this.original = original;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    public AssertStmt getOriginal() {
        return original == null ? this : original;
    }
}
