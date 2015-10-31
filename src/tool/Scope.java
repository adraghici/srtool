package tool;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class Scope {
    private final IdMap idMap;
    private String pred;
    private String ass;
    private Map<String, Integer> ids;

    private Scope(IdMap idMap, String pred, String ass) {
        this.idMap = idMap;
        this.pred = pred;
        this.ass = ass;
        this.ids = new HashMap<>();
    }

    public static Scope create(IdMap idMap) {
        return new Scope(idMap, "", "");
    }

    public static Scope fromScope(Scope scope) {
        Scope copy = create(scope.idMap);
        copy.ass = scope.ass;
        copy.pred = scope.pred;
        copy.ids = new HashMap<>(scope.ids);
        return copy;
    }

    public static Scope fromScope(Scope scope, String pred, String ass) {
        Scope copy = create(scope.idMap);
        copy.pred = pred;
        copy.ass = ass;
        copy.ids = new HashMap<>(scope.ids);
        return copy;
    }

    public String getPred() {
        return pred;
    }

    public String getAss() {
        return ass;
    }

    public void setAss(String ass) {
        this.ass = ass;
    }

    public void declareVar(String var) {
        updateVar(var, idMap.fresh(var));
    }

    public boolean hasVar(String var) {
        return ids.containsKey(var);
    }

    public int getId(String var) {
        if (!ids.containsKey(var)) {
            updateVar(var, idMap.fresh(var));
        }
        return ids.get(var);
    }

    /**
     * Increases the id of the given variable from the fresh id provider and returns the new id.
     */
    public int increaseVar(String var) {
        int id = idMap.fresh(var);
        updateVar(var, id);
        return id;
    }

    public void updateVar(String var, int id) {
        ids.put(var, id);
    }

    // TODO: havoc(x) modifies modset. New declaration of int x also alters the modset.
    public Set<String> modset(Scope scope) {
        return scope.ids.keySet().stream()
            .filter(var -> scope.ids.containsKey(var) && ids.get(var) != scope.ids.get(var))
            .collect(Collectors.toSet());
    }
}
