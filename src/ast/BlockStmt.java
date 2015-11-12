package ast;

import com.google.common.collect.Lists;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class BlockStmt implements Stmt {
    private final List<Stmt> stmts;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public Set<String> getModset() {
        return stmts.stream().map(Stmt::getModset).flatMap(Set::stream).collect(Collectors.toSet());
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(stmts);
    }
}
