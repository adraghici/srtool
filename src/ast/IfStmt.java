package ast;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Optional;
import java.util.Set;

public class IfStmt implements Condition, Stmt {
    private List<Node> children;

    public IfStmt(Expr condition, BlockStmt thenBlock, Optional<BlockStmt> elseBlock) {
        this.children = Lists.newArrayList(condition, thenBlock);
        elseBlock.ifPresent(this.children::add);
    }

    public BlockStmt getThenBlock() {
        return (BlockStmt) children.get(1);
    }

    public Optional<BlockStmt> getElseBlock() {
        return (children.size() == 2) ? Optional.empty() : Optional.of((BlockStmt) children.get(2));
    }

    @Override
    public Expr getCondition() {
        return (Expr) children.get(0);
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
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
