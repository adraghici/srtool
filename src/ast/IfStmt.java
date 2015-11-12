package ast;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Optional;
import java.util.Set;

public class IfStmt implements Condition, Stmt {
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
    public Set<String> getModset() {
        return Sets.union(
            thenBlock.getModset(),
            elseBlock.isPresent() ? elseBlock.get().getModset() : ImmutableSet.of()).immutableCopy();
    }

    @Override
    public List<Node> getChildren() {
        List<Node> children = Lists.newArrayList(condition, thenBlock);
        elseBlock.ifPresent(children::add);
        return children;
    }
}
