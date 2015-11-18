package ast;

import visitor.Visitor;

import java.util.Optional;

public class AssertStmt implements Condition, Stmt {
    private final Expr condition;
    private final AssertStmt original;

    public AssertStmt(Expr condition, Optional<AssertStmt> original) {
        this.condition = condition;
        this.original = original.orElse(this);
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
        return original;
    }
}
