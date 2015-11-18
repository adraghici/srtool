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

        for (int i = 0; i < depth; ++i) {
            List<Stmt> ifStmts = whileStmt.getWhileBlock().getStmts().stream()
                .map(stmt -> (Stmt) stmt.accept(this))
                .collect(Collectors.toList());
            ifStmts.add(result);
            result = new IfStmt(whileCondition, new BlockStmt(ifStmts), Optional.empty());
        }

        return result;
    }

    @Override
    public String getDescription() {
        return "Loop unwinding visitor";
    }
}
