package visitor;

import ast.*;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.Optional;

public class WhileVisitor implements Visitor {

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        List<Stmt> stmts = Lists.newArrayList();

        whileStmt.getInvariants().forEach(x -> stmts.add(new AssertStmt(x.getCondition())));
        whileStmt.getModified().forEach(x -> stmts.add(new HavocStmt(new VarRef(x))));
        whileStmt.getInvariants().forEach(x -> stmts.add(new AssumeStmt(x.getCondition())));

        List<Stmt> ifStmts = Lists.newArrayList();
        whileStmt.getWhileBlock().getStmts().forEach(ifStmts::add);
        whileStmt.getInvariants().forEach(x -> ifStmts.add(new AssertStmt(x.getCondition())));
        ifStmts.add(new AssumeStmt(new NumberExpr("0")));

        stmts.add(new IfStmt(whileStmt.getCondition(), new BlockStmt(ifStmts), Optional.empty()));

        return new BlockStmt(stmts);
    }

}
