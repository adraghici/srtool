package visitor;

import ast.*;
import com.google.common.collect.Lists;
import tool.AssertCollector;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class UnwindingVisitor extends DefaultVisitor {
    private final int depth;
    private final AssertCollector unwindingAssertCollector;

    public UnwindingVisitor(AssertCollector unwindingAssertCollector, int depth) {
        this.depth = depth;
        this.unwindingAssertCollector = unwindingAssertCollector;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        Expr whileCondition = whileStmt.getCondition();
        NumberExpr falseExpr = new NumberExpr("0");
        AssertStmt unwindingAssertStmt = new AssertStmt(falseExpr, Optional.empty());
        unwindingAssertCollector.add(Optional.empty(), unwindingAssertStmt);
        IfStmt result = new IfStmt(
            whileCondition,
            new BlockStmt(Lists.newArrayList(
                unwindingAssertStmt,
                new AssumeStmt(falseExpr))),
            Optional.empty());

        List<Stmt> invariantAsserts = whileStmt.getInvariants().stream()
            .map(inv -> new AssertStmt(inv.getCondition(), Optional.empty()))
            .collect(Collectors.toList());
        for (int i = 0; i < depth; ++i) {
            List<Stmt> ifStmts = whileStmt.getWhileBlock().getStmts().stream()
                .map(stmt -> (Stmt) stmt.accept(this))
                .collect(Collectors.toList());
            List<Stmt> stmts = Lists.newArrayList();
            stmts.addAll(ifStmts);
            stmts.addAll(invariantAsserts);
            stmts.add(result);
            result = new IfStmt(whileCondition, new BlockStmt(stmts), Optional.empty());
        }

        List<Stmt> stms = Lists.newArrayList(invariantAsserts);
        stms.add(result);
        return new BlockStmt(stms);
    }

    @Override
    public String getDescription() {
        return "Loop unwinding visitor";
    }
}
