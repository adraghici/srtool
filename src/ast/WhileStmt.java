package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class WhileStmt implements Condition, Stmt {
    private List<Node> children;

    public WhileStmt(Expr condition, BlockStmt whileBlock, List<LoopInvariant> invariants) {
        this.children = Lists.newArrayList(condition, whileBlock);
        this.children.addAll(invariants);
    }

    public List<LoopInvariant> getInvariants() {
        return children.stream()
            .filter(x -> x instanceof LoopInvariant)
            .map(x -> (LoopInvariant) x)
            .collect(Collectors.toList());
    }

    public BlockStmt getWhileBlock() {
        return (BlockStmt) children.get(1);
    }

    @Override
    public Expr getCondition() {
        return (Expr) children.get(0);
    }

    @Override
    public Set<String> getModified() {
        return getWhileBlock().getModified();
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
