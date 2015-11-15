package visitor;

import ast.*;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.Optional;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class LoopUnwindingVisitor implements Visitor {
    private final int depth;

    public LoopUnwindingVisitor() {
        depth = 3;
    }

    @Override public Stmt visit(WhileStmt whileStmt) {
        Expr whileCondition = whileStmt.getCondition();

        IfStmt result = new IfStmt(whileCondition,
            new BlockStmt(Lists.newArrayList(new AssumeStmt(new NumberExpr("0")))),
            Optional.empty());

        for (int i = 0; i < depth; ++i) {
            List<Stmt> ifStmts = Lists.newArrayList(whileStmt.getWhileBlock().getStmts());
            ifStmts.add(result);
            result = new IfStmt(whileCondition, new BlockStmt(ifStmts), Optional.empty());
        }

        return result;
    }
}
