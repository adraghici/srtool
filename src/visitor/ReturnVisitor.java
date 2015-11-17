package visitor;

import ast.AssertStmt;
import ast.Expr;
import ast.Node;
import ast.NumberExpr;
import ast.Postcondition;
import ast.ProcedureDecl;
import ast.Stmt;
import com.google.common.collect.Maps;
import tool.SMTUtil;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Visitor used to transform postconditions using the result from the return statement to asserts
 * put at the end.
 */
public class ReturnVisitor implements Visitor {

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        List<Stmt> stmts = procedureDecl.getStmts();
        stmts.addAll(
            createPostconditionAsserts(
                procedureDecl.getPostconditions(),
                procedureDecl.getReturnExpr()));
        return new ProcedureDecl(
            procedureDecl.getName(),
            procedureDecl.getParams(),
            procedureDecl.getConditions(),
            stmts,
            new NumberExpr("not needed anymore"));
    }

    @Override
    public String getDescription() {
        return "Return visitor";
    }

    public List<AssertStmt> createPostconditionAsserts(
        List<Postcondition> postconditions,
        Expr returnExpr) {
        Map<String, Expr> substitutes = Maps.newHashMap();
        substitutes.put(SMTUtil.RESULT_PLACEHOLDER, returnExpr);
        return postconditions.stream()
            .map(p -> new AssertStmt(p.getCondition().replace(substitutes)))
            .collect(Collectors.toList());
    }
}
