// Synthetic inputs for analytic tests.
export const circuitFixture = {
  driver: {
    fsHz: 25,
    vasM3: 0.08,
    qes: 0.45,
    qms: 8,
    reOhms: 6,
    leHenries: 0,
    sdM2: 0.05,
  },
  volumeM3: 0.07,
  voltageRms: 2.83,
  medium: { densityKgM3: 1.2041, soundSpeedMps: 343 },
  leakageQuality: Infinity,
  absorptionQuality: Infinity,
}
