import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  startNewSession,
  isSessionCurrent,
  RunSession,
} from "../../../vscode_extension/src/run-session.js";

/**
 * Property 2: Session currentness exclusivity
 * Validates: Requirements 1.3
 *
 * For any sequence of created sessions, isSessionCurrent(session) SHALL return
 * true for exactly one session (the last created) and false for all others.
 */
describe("Property 2: Session currentness exclusivity", () => {
  it("isSessionCurrent returns true for exactly the last created session, false for all others", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string({ minLength: 1, maxLength: 20 }), {
          minLength: 1,
          maxLength: 20,
        }),
        (fileNames) => {
          // Create N sessions, collecting all of them
          const sessions: RunSession[] = fileNames.map((f) =>
            startNewSession(f),
          );

          const lastSession = sessions[sessions.length - 1];

          // Only the last session should be current
          for (let i = 0; i < sessions.length - 1; i++) {
            expect(isSessionCurrent(sessions[i])).toBe(false);
          }
          expect(isSessionCurrent(lastSession)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });
});
