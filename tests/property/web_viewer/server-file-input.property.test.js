import { strict as assert } from 'node:assert';
import { test, describe } from 'node:test';
import fc from 'fast-check';
import { computeCoverage } from '../../../web_viewer/server.js';

/**
 * Validates: Requirements 3.7
 *
 * Feature: proofpulse-restructure, Property 1: Invalid file path rejection
 *
 * For any string that does not correspond to an existing file with a .dfy
 * extension, computeCoverage() SHALL throw with an httpStatus of 400 or 404
 * and a non-empty error message in httpBody.error.
 *
 * Covers: nonexistent paths, wrong extensions, empty strings, directory paths,
 * paths with special characters, whitespace-only strings.
 */
describe('Feature: proofpulse-restructure, Property 1: Invalid file path rejection', () => {
  test('random non-.dfy strings cause computeCoverage to throw 4xx with error message', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.oneof(
          // Arbitrary strings (most won't exist on disk)
          fc.string({ minLength: 0, maxLength: 200 }),
          // Whitespace-only strings
          fc.stringOf(fc.constantFrom(' ', '\t', '\n', '\r'), { minLength: 1, maxLength: 20 }),
          // Paths with special characters
          fc.stringOf(
            fc.constantFrom('/', '\\', '..', '*', '?', '<', '>', '|', ':', '"', '\0', ' ', 'a', 'z', '0', '.'),
            { minLength: 1, maxLength: 50 }
          ),
          // Strings with wrong extensions
          fc.tuple(fc.string({ minLength: 1, maxLength: 30 }), fc.constantFrom('.txt', '.py', '.js', '.rs', '.c', '')).map(([name, ext]) => name + ext),
          // Empty string
          fc.constant('')
        ),
        async (filePath) => {
          try {
            await computeCoverage(filePath);
            // If it didn't throw, the path was a real .dfy file — skip this case
            // (extremely unlikely with random strings, but be safe)
            assert.fail(`Expected computeCoverage to throw for input: ${JSON.stringify(filePath)}`);
          } catch (err) {
            // If it's our assert.fail, rethrow
            if (err.code === 'ERR_ASSERTION') throw err;

            assert.ok(
              err.httpStatus === 400 || err.httpStatus === 404,
              `Expected httpStatus 400 or 404, got ${err.httpStatus} for input: ${JSON.stringify(filePath)}`
            );
            assert.ok(
              typeof err.httpBody === 'object' && err.httpBody !== null,
              `Expected httpBody to be an object for input: ${JSON.stringify(filePath)}`
            );
            assert.ok(
              typeof err.httpBody.error === 'string' && err.httpBody.error.length > 0,
              `Expected non-empty httpBody.error string for input: ${JSON.stringify(filePath)}`
            );
          }
        }
      ),
      { numRuns: 100 }
    );
  });
});
