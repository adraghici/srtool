package util;

import ast.AssertStmt;
import ast.Program;
import tool.ConstraintSolution;
import tool.SMTGenerator;
import tool.SMTModel;
import visitor.Visitor;

import java.util.List;
import java.util.stream.Collectors;

public class StrategyUtil {
    public static final int BMC_START_DEPTH = 5;
    public static final int BMC_STEP = 3;

    /**
     * Returns the list of asserts failed in the given model.
     */
    public static List<AssertStmt> getFailedAsserts(SMTModel smtModel, ConstraintSolution solution) {
        return SMTUtil.failedAssertionIds(solution.getDetails()).stream()
            .map(smtModel::getAssert)
            .collect(Collectors.toList());
    }

    /**
     * Generates and {@link SMTModel} by applying the given visitors along with the SMT generator
     * to the given program.
     */
    public static SMTModel generateSMT(Program program, List<Visitor> visitors, List<String> states) {
        Program transformed = ProgramUtil.transform(program, visitors, states);
        SMTGenerator smtGenerator = new SMTGenerator(transformed);
        return smtGenerator.generateSMT();
    }
}
