package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class WhileStmt implements Condition, Stmt {
    private final Expr condition;
    private final BlockStmt whileBlock;
    private final List<LoopInvariant> invariants;
    private List<Node> children;

    public WhileStmt(Expr condition, BlockStmt whileBlock, List<LoopInvariant> invariants) {
        this.condition = condition;
        this.whileBlock = whileBlock;
        this.invariants = invariants;
        this.children = Lists.newArrayList(condition, whileBlock);
        this.children.addAll(invariants);
        this.children.addAll(invariants);
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
        return whileBlock.getModified();
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
