package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class BlockStmt implements Stmt {
    private final List<Stmt> stmts;
    private List<Node> children;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
        this.children = Lists.newArrayList(stmts);
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public Set<String> getModified() {
        return stmts.stream().map(Stmt::getModified).flatMap(Set::stream).collect(Collectors.toSet());
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
