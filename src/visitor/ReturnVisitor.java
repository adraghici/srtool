package visitor;

import ast.AssertStmt;
import ast.Expr;
import ast.Node;
import ast.NumberExpr;
import ast.Postcondition;
import ast.PrePostCondition;
import ast.ProcedureDecl;
import ast.Stmt;
import com.google.common.collect.Maps;
import tool.AssertCollector;
import util.SMTUtil;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Visitor used to transform postconditions using the result from the return statement to asserts
 * put at the end.
 */
public class ReturnVisitor extends DefaultVisitor {
    public ReturnVisitor(AssertCollector assertCollector) {
        super(assertCollector);
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        List<Stmt> stmts = procedureDecl.getStmts().stream()
            .map(stmt -> (Stmt) stmt.accept(this))
            .collect(Collectors.toList());
        stmts.addAll(
            createPostconditionAsserts(procedureDecl.getPostconditions(), procedureDecl.getReturnExpr()));
        List<PrePostCondition> conditions = procedureDecl.getConditions().stream()
            .map(cond -> (PrePostCondition) cond.accept(this))
            .collect(Collectors.toList());
        return new ProcedureDecl(
            procedureDecl.getName(),
            procedureDecl.getParams(),
            conditions,
            stmts,
            new NumberExpr("not needed anymore"));
    }

    @Override
    public String getDescription() {
        return "Return visitor";
    }

    public List<AssertStmt> createPostconditionAsserts(List<Postcondition> postconditions, Expr returnExpr) {
        Map<String, Expr> substitutes = Maps.newHashMap();
        substitutes.put(SMTUtil.RESULT_PLACEHOLDER, returnExpr);

        return postconditions.stream()
            .map(p -> {
                AssertStmt assertStmt = new AssertStmt(p.getCondition().replace(substitutes));
                assertCollector.add(p, assertStmt);
                return assertStmt;
            })
            .collect(Collectors.toList());
    }
}
