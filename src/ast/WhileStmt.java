package ast;

import com.google.common.collect.Lists;

import java.util.List;
import java.util.Optional;

public class WhileStmt implements Condition, Stmt {
    private final Expr condition;
    private final BlockStmt whileBlock;
    private final Optional<List<LoopInvariant>> invariants;

    public WhileStmt(Expr condition, BlockStmt whileBlock, Optional<List<LoopInvariant>> invariants) {
        this.condition = condition;
        this.whileBlock = whileBlock;
        this.invariants = invariants;
    }

    public Optional<List<LoopInvariant>> getInvariants() {
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
    public List<Node> getChildren() {
        List<Node> children = Lists.newArrayList(condition, whileBlock);
        invariants.ifPresent(children::addAll);
        return children;
    }
}
