package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

/**
 * Created by costica1234 on 18/10/15.
 */
public class VCGeneratorVisitor extends SimpleCBaseVisitor<StringBuilder> {

    private SSAMap ssaMap;

    public VCGeneratorVisitor() {
        ssaMap = new SSAMap();
    }

    @Override
    public StringBuilder visitProgram(ProgramContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarDecl(VarDeclContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitProcedureDecl(ProcedureDeclContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitFormalParam(FormalParamContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitPrepost(PrepostContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitRequires(RequiresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitEnsures(EnsuresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateRequires(CandidateRequiresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitStmt(StmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitAssignStmt(AssignStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitAssertStmt(AssertStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitAssumeStmt(AssumeStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitHavocStmt(HavocStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitIfStmt(IfStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitWhileStmt(WhileStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitBlockStmt(BlockStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitLoopInvariant(LoopInvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitInvariant(InvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateInvariant(CandidateInvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitExpr(ExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitTernExpr(TernExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitLorExpr(LorExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitLandExpr(LandExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitBorExpr(BorExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitBxorExpr(BxorExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitBandExpr(BandExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitEqualityExpr(EqualityExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitRelExpr(RelExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitShiftExpr(ShiftExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitAddExpr(AddExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitMulExpr(MulExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitUnaryExpr(UnaryExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitAtomExpr(AtomExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitNumberExpr(NumberExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarrefExpr(VarrefExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitParenExpr(ParenExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitResultExpr(ResultExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitOldExpr(OldExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarref(VarrefContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarIdentifier(VarIdentifierContext ctx) {
        return null;
    }

}
