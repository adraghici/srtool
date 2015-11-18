package visitor;

import ast.AssertStmt;
import ast.CandidatePostcondition;
import ast.Expr;
import ast.Node;
import ast.NumberExpr;
import ast.Postcondition;
import ast.ProcedureDecl;
import ast.Stmt;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import tool.AssertCollector;
import util.SMTUtil;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to transform postconditions using the result from the return statement to asserts
 * put at the end.
 */
public class ReturnVisitor extends DefaultVisitor {
    private final boolean considerCandidates;
    private final AssertCollector assertCollector;

    public static ReturnVisitor withCandidates(AssertCollector assertCollector) {
        return new ReturnVisitor(assertCollector, true);
    }

    public static ReturnVisitor withoutCandidates(AssertCollector assertCollector) {
        return new ReturnVisitor(assertCollector, false);
    }

    private ReturnVisitor(AssertCollector assertCollector, boolean considerCandidates) {
        visitStage = VisitStage.DIRTY;
        this.considerCandidates = considerCandidates;
        this.assertCollector = assertCollector;
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        List<Stmt> stmts = procedureDecl.getStmts();
        stmts.addAll(
            createPostconditionAsserts(
                procedureDecl.getPostconditions(),
                procedureDecl.getCandidatePostconditions(),
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
        List<CandidatePostcondition> candidatePostconditions,
        Expr returnExpr) {
        Map<String, Expr> substitutes = Maps.newHashMap();
        substitutes.put(SMTUtil.RESULT_PLACEHOLDER, returnExpr);

        List<AssertStmt> postAsserts = postconditions.stream()
            .map(p -> new AssertStmt(p.getCondition().replace(substitutes), Optional.empty()))
            .collect(Collectors.toList());
        List<AssertStmt> result = Lists.newArrayList(postAsserts);
        if (considerCandidates) {
            List<AssertStmt> candidatePostAsserts = candidatePostconditions.stream()
                .map(post -> {
                    AssertStmt assertStmt = new AssertStmt(post.getCondition().replace(substitutes), Optional.empty());
                    assertCollector.add(Optional.of(post), assertStmt);
                    return assertStmt;
                }).collect(Collectors.toList());
            result.addAll(candidatePostAsserts);
        }

        return result;
    }
}
