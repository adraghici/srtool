package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap {
    private static final Integer DEFAULT_ID = 0;
    private final Map<String, Integer> nextID;

    public SSAMap() {
        this.nextID = new HashMap<>();
    }

    public SSAMap(Map<String, Integer> nextID) {
        this.nextID = nextID;
    }

    public int id(String var) {
        if (nextID.containsKey(var)) {
            return nextID.get(var);
        }
        return DEFAULT_ID;
    }

    public int fresh(String var) {
        nextID.put(var, id(var) + 1);
        return id(var);
    }

    public Map<String, Integer> getMap() {
        return nextID;
    }
}
