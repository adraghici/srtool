package ast;

import com.google.common.collect.Lists;

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
    public Set<String> getModset() {
        return whileBlock.getModset();
    }

    @Override
    public List<Node> getChildren() {
        List<Node> children = Lists.newArrayList(condition, whileBlock);
        children.addAll(invariants);
        return children;
    }
}
