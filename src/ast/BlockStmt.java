package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class BlockStmt implements Stmt {
    private final List<Stmt> stmts;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(stmts);
    }
}
