package ast;

import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class WhileStmt implements Condition, Stmt {
    private final Expr condition;
    private final BlockStmt whileBlock;
    private final List<LoopInvariant> invariants;

    public WhileStmt(Expr condition, BlockStmt whileBlock, List<LoopInvariant> invariants) {
        this.condition = condition;
        this.whileBlock = whileBlock;
        this.invariants = invariants;
    }

    public List<LoopInvariant> getInvariants() {
        return invariants;
    }

    public BlockStmt getWhileBlock() {
        return whileBlock;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Set<String> getModified() {
        return getWhileBlock().getModified();
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
