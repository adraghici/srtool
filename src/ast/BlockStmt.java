package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class BlockStmt implements Stmt {
    private List<Node> children;

    public BlockStmt(List<Stmt> stmts) {
        this.children = Lists.newArrayList(stmts);
    }

    public List<Stmt> getStmts() {
        return children.stream().map(x -> (Stmt) x).collect(Collectors.toList());
    }

    @Override
    public Set<String> getModified() {
        return getStmts().stream().map(Stmt::getModified).flatMap(Set::stream).collect(Collectors.toSet());
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
