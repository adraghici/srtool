package ast;

import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class BlockStmt implements Stmt {
    private List<Stmt> stmts;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public Set<String> getModified() {
        return getStmts().stream().map(Stmt::getModified).flatMap(Set::stream).collect(Collectors.toSet());
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
