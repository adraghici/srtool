package ast;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Optional;
import java.util.Set;

public class IfStmt implements Condition, Stmt {
    private List<Node> children;
    private final Expr condition;
    private final BlockStmt thenBlock;
    private final Optional<BlockStmt> elseBlock;

    public IfStmt(Expr condition, BlockStmt thenBlock, Optional<BlockStmt> elseBlock) {
        this.condition = condition;
        this.thenBlock = thenBlock;
        this.elseBlock = elseBlock;
    }

    public BlockStmt getThenBlock() {
        return thenBlock;
    }

    public Optional<BlockStmt> getElseBlock() {
        return elseBlock;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Set<String> getModified() {
        return Sets.union(
            getThenBlock().getModified(),
            getElseBlock().isPresent()
                ? getElseBlock().get().getModified()
                : ImmutableSet.of()).immutableCopy();
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
