package visitor;

import ast.*;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class UnwindingVisitor extends DefaultVisitor {
    private final int depth;

    public UnwindingVisitor(int depth) {
        this.depth = depth;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        Expr whileCondition = whileStmt.getCondition();

        IfStmt result = new IfStmt(
            whileCondition,
            new BlockStmt(Lists.newArrayList(new AssumeStmt(new NumberExpr("0")))),
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
