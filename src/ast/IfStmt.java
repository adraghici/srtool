package ast;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Optional;
import java.util.Set;

public class IfStmt implements Condition, Stmt {
    private final Expr condition;
    private final BlockStmt thenBlock;
    private final Optional<BlockStmt> elseBlock;
    private final List<Node> children;

    public IfStmt(Expr condition, BlockStmt thenBlock, Optional<BlockStmt> elseBlock) {
        this.condition = condition;
        this.thenBlock = thenBlock;
        this.elseBlock = elseBlock;
        this.children = Lists.newArrayList(condition, thenBlock);
        elseBlock.ifPresent(children::add);
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
            thenBlock.getModified(),
            elseBlock.isPresent() ? elseBlock.get().getModified() : ImmutableSet.of()).immutableCopy();
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
